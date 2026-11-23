import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.Read191
open CircuitLowerBounds
private theorem agree_fold (i : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, i ∉ g.inputs)
    (a b : List Bool) (hl : a.length = b.length) (hi : i < a.length)
    (ha : ∀ j, j ≠ i → a.getD j false = b.getD j false) :
    ∀ j, j ≠ i →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) a).getD j false =
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) b).getD j false := by
  induction gs generalizing a b with
  | nil => exact ha
  | cons g gs ih =>
    have hh : g.inputs.map (fun k => a.getD k false) = g.inputs.map (fun k => b.getD k false) := by
      apply List.map_congr_left
      intro k hk
      apply ha
      rintro rfl
      exact h g (by simp) hk
    simp only [List.foldl_cons]
    rw [hh]
    apply ih (fun z hz => h z (by simp [hz]))
    · simp [hl]
    · simp; omega
    · intro j hj
      simp only [List.getD_eq_getElem?_getD]
      by_cases hj' : j < a.length
      · rw [List.getElem?_append_left hj', List.getElem?_append_left (hl ▸ hj')]
        exact ha j hj
      · rw [List.getElem?_append_right (by omega),List.getElem?_append_right (by omega),hl]
theorem essential_read {n : ℕ} (C : Circuit) (i : Fin n)
    (x y : Fin n → Bool) (he : ∀ j, j ≠ i → x j = y j)
    (hv : C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    C.output = i.val ∨ ∃ g ∈ C.gates, i.val ∈ g.inputs := by
  by_contra! hn
  apply hv
  apply agree_fold i C.gates hn.2
  · simp
  · simpa using i.isLt
  · intro j hj
    by_cases hj' : j < n
    · simpa [List.getD_eq_getElem?_getD,hj'] using he ⟨j,hj'⟩ (by intro e; exact hj (congrArg Fin.val e))
    · simp [List.getD_eq_getElem?_getD,hj']
  · exact hn.1
end PEqualNP.Outside.Read191
namespace PEqualNP.Outside.Read191
open CircuitLowerBounds
def active (g : Gate) : List ℕ := match g.op with | .not => g.inputs.take 1 | _ => g.inputs
def trim (g : Gate) : Gate := ⟨g.op, active g⟩
private theorem trim_eval (g : Gate) (w : List Bool) :
    (trim g).op.eval ((trim g).inputs.map fun k => w.getD k false) =
    g.op.eval (g.inputs.map fun k => w.getD k false) := by
  cases g with
  | mk op ins => cases op <;> cases ins <;> rfl
private theorem trim_wires (C : Circuit) (x : List Bool) :
    (Circuit.mk (C.gates.map trim) C.output).wires x = C.wires x := by
  simp only [Circuit.wires, List.foldl_map]
  congr 1
  funext w g
  rw [trim_eval]
def path (x : Fin 5 → Bool) := decide (∃ i j : Fin 5, i.val+1=j.val ∧ x i=true ∧ x j=true)
private theorem sensitive : ∀ i : Fin 5, ∃ x y : Fin 5 → Bool,
    (∀ k, k ≠ i → x k = y k) ∧ path x ≠ path y := by decide
private theorem prefix191 (gs : List Gate) (w : List Bool) :
    ∃ tail, gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun k => a.getD k false)]) w = w ++ tail := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp⟩
  | cons g gs ih =>
    obtain ⟨tail,h⟩ := ih (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    exact ⟨_, h.trans (List.append_assoc ..)⟩
theorem output_ge (C : Circuit) (hc : MetaComplexity.circuitFun 5 C = path) : 5 ≤ C.output := by
  by_contra! h
  let i : Fin 5 := ⟨C.output,h⟩
  let x : Fin 5 → Bool := fun j => decide (j=i)
  have off : ∀ k : Fin 5, path (fun j => decide (j=k)) = false := by decide
  obtain ⟨t,ht⟩ := prefix191 C.gates (List.ofFn x)
  have hh := congrFun hc x
  change (C.wires (List.ofFn x)).getD C.output false = path x at hh
  rw [show C.wires (List.ofFn x) = List.ofFn x ++ t from ht,
      List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using h),off i] at hh
  simp only [List.getElem?_ofFn, dif_pos h, Option.getD_some] at hh
  have yes : x ⟨C.output,h⟩ = true := by simp [x,i]
  exact Bool.noConfusion (yes.symm.trans hh)
theorem path_reads (C : Circuit) (hc : MetaComplexity.circuitFun 5 C = path) (i : Fin 5) :
    ∃ g ∈ C.gates, i.val ∈ active g := by
  obtain ⟨x,y,hxy,hne⟩ := sensitive i
  have hg := output_ge C hc
  let D := Circuit.mk (C.gates.map trim) C.output
  have hD (z : Fin 5 → Bool) : D.eval (List.ofFn z) = path z := by
    unfold Circuit.eval
    rw [trim_wires]
    exact congrFun hc z
  obtain h | ⟨g,hmem,hr⟩ := essential_read D i x y hxy (by simpa only [hD] using hne)
  · change C.output = i.val at h; omega
  · obtain ⟨g',hm,rfl⟩ := List.mem_map.mp hmem
    exact ⟨g',hm,hr⟩
end PEqualNP.Outside.Read191
namespace PEqualNP.Outside.Read191
open CircuitLowerBounds MetaComplexity
def trimmed (C : Circuit) : Circuit := ⟨C.gates.map trim,C.output⟩
theorem trimmed_fun (C : Circuit) (n : ℕ) : circuitFun n (trimmed C) = circuitFun n C := by
  funext x
  change ((trimmed C).wires _).getD _ _ = _
  rw [show (trimmed C).wires (List.ofFn x) = C.wires (List.ofFn x) from trim_wires C _]; rfl
theorem trimmed_min (C : Circuit) {n : ℕ} (hm : IsMinimalCircuit n C) : IsMinimalCircuit n (trimmed C) := by
  constructor
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop,hsize⟩ := hm.1 a ha
    refine ⟨hop,?_⟩
    change (active a).length ≤ 2
    cases hh : a.op <;> simp [active,hh,hsize]
  · intro D hD hs
    have hh := hm.2 D hD (hs.trans (trimmed_fun C n))
    simpa [trimmed,Circuit.size] using hh
end PEqualNP.Outside.Read191

namespace PEqualNP.Outside.Live191
open CircuitLowerBounds MetaComplexity

private def lower (h i : ℕ) := if i < h then i else i-1
private def ren (h : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (lower h)⟩
private def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read (w t : List Bool) (z : Bool) (i : ℕ) (hn : i ≠ w.length) :
    (w++t).getD (lower w.length i) false = (w++(z::t)).getD i false := by
  by_cases hi : i < w.length
  · simp only [lower, ite_eq_left hi, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · obtain ⟨k,hk⟩ : ∃ k, i = w.length + (k+1) := ⟨i-w.length-1, by omega⟩
    subst i
    simp [lower, List.getElem?_append_right, List.getD_eq_getElem?_getD]

private theorem suffix (gs : List Gate) (w t : List Bool) (z : Bool) (out : ℕ)
    (ho : out ≠ w.length) (hd : ∀ g ∈ gs, w.length ∉ g.inputs) :
    ((gs.map (ren w.length)).foldl step (w++t)).getD (lower w.length out) false =
    (gs.foldl step (w++(z::t))).getD out false := by
  induction gs generalizing t with
  | nil => exact read w t z out ho
  | cons g gs ih =>
    have hh : (ren w.length g).op.eval ((ren w.length g).inputs.map fun i => (w++t).getD i false) =
        g.op.eval (g.inputs.map fun i => (w++(z::t)).getD i false) := by
      unfold ren
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact read w t z i fun he => hd g (by simp) (he ▸ hi)
    let v := g.op.eval (g.inputs.map fun i => (w++(z::t)).getD i false)
    simpa only [List.map_cons,List.foldl_cons,step,hh,List.append_assoc,List.cons_append] using
      (ih (t++[v]) (fun g hg => hd g (List.mem_cons_of_mem _ hg)))

private theorem run_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih,step]; omega

theorem live {n : ℕ} (C : Circuit) (hm : IsMinimalCircuit n C) (p : ℕ)
    (hp : p < C.gates.length) (ho : C.output ≠ n+p) :
    ∃ q : Fin C.gates.length, p < q.val ∧ n+p ∈ (C.gates.get q).inputs := by
  by_contra hno
  let pre := C.gates.take p
  let post := C.gates.drop (p+1)
  let g := C.gates[p]
  have hs : pre ++ g :: post = C.gates := by
    rw [show g :: post = C.gates.drop p from (List.drop_eq_getElem_cons hp).symm]
    exact List.take_append_drop ..
  have lp : pre.length = p := by simp [pre, Nat.min_eq_left (by omega : p ≤ C.gates.length)]
  have hd : ∀ u ∈ post, n+p ∉ u.inputs := by
    intro u hu hread
    obtain ⟨k,hk,huk⟩ := List.getElem_of_mem hu
    have hkb : p+1+k < C.gates.length := by simp [post] at hk; omega
    apply hno
    refine ⟨⟨p+1+k,hkb⟩,show p < p+1+k by omega,?_⟩
    rw [← huk] at hread
    simpa [post,List.getElem_drop] using hread
  let D : Circuit := ⟨pre++post.map (ren (n+p)), lower (n+p) C.output⟩
  have hf : FanInTwo D := by
    intro u hu
    change u ∈ pre ++ post.map (ren (n+p)) at hu
    rcases List.mem_append.mp hu with h | h
    · apply hm.1 u (hs ▸ List.mem_append_left _ h)
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      have h := hm.1 v (hs ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hv))
      simpa [ren] using h
  have eq : circuitFun n D = circuitFun n C := by
    funext x
    let w := pre.foldl step (List.ofFn x)
    have lw : w.length = n+p := by simp [w,run_len,lp]
    let z := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hx := suffix post w [] z C.output (lw ▸ ho) (lw ▸ hd)
    change ((pre++post.map (ren (n+p))).foldl step (List.ofFn x)).getD _ false =
      (C.gates.foldl step (List.ofFn x)).getD _ false
    rw [← hs, List.foldl_append, List.foldl_append]
    simpa only [lw, List.append_nil, w, z, D, List.foldl_cons, step] using hx
  have le := hm.2 D hf eq
  change C.gates.length ≤ (pre++post.map (ren (n+p))).length at le
  have lens := congrArg List.length hs
  simp only [List.length_append,List.length_cons,List.length_map] at le lens
  omega

end PEqualNP.Outside.Live191
namespace PEqualNP.Outside.Read191
open CircuitLowerBounds MetaComplexity
theorem last_output {n : ℕ} (C : Circuit) (hm : IsMinimalCircuit n C) (hp : 0 < C.gates.length) :
    C.output = n + (C.gates.length-1) := by
  by_contra ho
  obtain ⟨q,hq,_⟩ := PEqualNP.Outside.Live191.live C hm (C.gates.length-1) (by omega) ho
  have := q.isLt
  omega
end PEqualNP.Outside.Read191
namespace PEqualNP.Outside.Tidy191
open CircuitLowerBounds MetaComplexity
def trimAt (k : ℕ) (g : Gate) : Gate :=
  let ins := g.inputs.filter (· < k)
  match g.op with
  | .and => if g.inputs.all (· < k) then g else ⟨.or,[]⟩
  | .or => ⟨.or,ins⟩
  | .not => ⟨.not,(g.inputs.take 1).filter (· < k)⟩
  | _ => ⟨.or,[]⟩
def ok (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def good (k : ℕ) (g : Gate) := ok g ∧ (∀ i ∈ g.inputs, i < k) ∧ (g.op = .not → g.inputs.length ≤ 1)
private theorem correct_one (g : Gate) (w : List Bool) (hg : ok g) :
    let g' := trimAt w.length g
    g'.op.eval (g'.inputs.map fun i => w.getD i false) = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op,l⟩ := g
  obtain ⟨hop,hl⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change l.length ≤ 2 at hl
  have bad (i : ℕ) (hi : ¬i < w.length) : w.getD i false = false := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)]
  cases l with
  | nil => rcases hop with rfl|rfl|rfl <;> rfl
  | cons a ls =>
    cases ls with
    | nil =>
      rcases hop with rfl|rfl|rfl <;> by_cases h : a < w.length <;> simp_all [trimAt, GateOp.eval] <;> rw [if_neg (by omega)] <;> rfl
    | cons b tail =>
      have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst tail
      rcases hop with rfl|rfl|rfl <;> by_cases h : a < w.length <;> by_cases h' : b < w.length <;> simp_all [trimAt,GateOp.eval] <;> rw [if_neg (by omega)] <;> rfl
private theorem good_one (k : ℕ) (g : Gate) (hg : ok g) : good k (trimAt k g) := by
  rcases g with ⟨op,l⟩
  obtain ⟨hop,hl⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change l.length ≤ 2 at hl
  rcases hop with rfl|rfl|rfl
  · by_cases h : l.all (· < k) = true
    · simpa [trimAt,good,ok,h,hl] using List.all_eq_true.mp h
    · simp [trimAt,good,ok,h]
  · simp [trimAt,good,ok,(List.length_filter_le ..).trans hl]
  · have h : ((l.take 1).filter (· < k)).length ≤ 1 := (List.length_filter_le ..).trans (by simp)
    simp [trimAt,good,ok,h,show ((l.take 1).filter (· < k)).length ≤ 2 by omega]
def trimList : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g::gs => trimAt k g :: trimList (k+1) gs
@[simp] theorem trim_length (k : ℕ) (gs : List Gate) : (trimList k gs).length = gs.length := by
  induction gs generalizing k <;> simp_all [trimList]
theorem trim_good (k : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, ok g) (i : ℕ) (g : Gate)
    (he : (trimList k gs)[i]? = some g) : good (k+i) g := by
  induction gs generalizing k i with
  | nil => simp [trimList] at he
  | cons a as ih =>
    cases i with
    | zero => simp [trimList] at he; subst g; exact good_one _ _ (h _ (by simp))
    | succ i =>
      have ht := ih (k+1) (fun b hb => h b (by simp [hb])) i he
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
private def run (gs : List Gate) (w : List Bool) := gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun k => a.getD k false)]) w
theorem run_trim (gs : List Gate) (w : List Bool) (h : ∀ g ∈ gs, ok g) : run (trimList w.length gs) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [trimList,run,List.foldl_cons]
    rw [correct_one g w (h g (by simp))]
    simpa [run] using ih (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) (fun a ha => h a (by simp [ha]))
end PEqualNP.Outside.Tidy191
namespace PEqualNP.Outside.Tidy191
open CircuitLowerBounds MetaComplexity
def asCircuit (n : ℕ) (C : Circuit) : Circuit := ⟨trimList n C.gates,C.output⟩
theorem same_wires {n : ℕ} (C : Circuit) (hf : FanInTwo C) (x : Fin n → Bool) :
    (asCircuit n C).wires (List.ofFn x) = C.wires (List.ofFn x) := by
  have h := run_trim C.gates (List.ofFn x) (fun g hg => hf g hg)
  simpa only [List.length_ofFn,asCircuit,Circuit.wires,run] using h
theorem same_fun {n : ℕ} (C : Circuit) (hf : FanInTwo C) : circuitFun n (asCircuit n C) = circuitFun n C := by
  funext x
  exact congrArg (fun w : List Bool => w.getD C.output false) (same_wires C hf x)
theorem as_min {n : ℕ} (C : Circuit) (hm : IsMinimalCircuit n C) : IsMinimalCircuit n (asCircuit n C) := by
  constructor
  · intro g hg
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
    exact (trim_good n C.gates (fun g hg => hm.1 g hg) i g hi).1
  · intro D hD he
    have h := hm.2 D hD (he.trans (same_fun C hm.1))
    simpa [asCircuit,Circuit.size] using h
end PEqualNP.Outside.Tidy191

namespace PEqualNP.Outside.L_meta_191_aux
open PEqualNP.CircuitLowerBounds

def ports (gs : List Gate) := gs.flatMap Gate.inputs

theorem ports_length (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (ports gs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [ports]
  | cons g gs ih =>
    have ht := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hh := h g (List.mem_cons_self ..)
    simp only [ports,List.flatMap_cons,List.length_append,List.length_cons] at *
    omega

theorem ports_cases (gs : List Gate) (hs : gs.length ≤ 5)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) (hread : ∀ i < 9, i ∈ ports gs) :
    (ports gs : Multiset ℕ) = Multiset.range 9 ∨
    ∃ w : ℕ, (ports gs : Multiset ℕ) = Multiset.range 9 + {w} := by
  have le : Multiset.range 9 ≤ (ports gs : Multiset ℕ) :=
    (Multiset.le_iff_subset (Multiset.nodup_range 9)).2 fun i hi => hread i (Multiset.mem_range.mp hi)
  obtain ⟨extra,he⟩ := Multiset.le_iff_exists_add.mp le
  have hc := congrArg Multiset.card he
  simp only [Multiset.coe_card,Multiset.card_add,Multiset.card_range] at hc
  have hl := ports_length gs h
  have hx : extra.card ≤ 1 := by omega
  by_cases hz : extra.card = 0
  · have : extra = 0 := Multiset.card_eq_zero.mp hz
    exact Or.inl (by simpa [this] using he)
  · obtain ⟨w,hw⟩ := Multiset.card_eq_one.mp (by omega : extra.card = 1)
    exact Or.inr ⟨w,by simpa [hw] using he⟩

end PEqualNP.Outside.L_meta_191_aux

namespace PEqualNP.Outside.L_meta_191_aux
open PEqualNP.CircuitLowerBounds

private def execGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def agree (bad : ℕ → Prop) (w w' : List Bool) :=
  w.length = w'.length ∧ ∀ i, ¬ bad i → w.getD i false = w'.getD i false

private theorem agree_append {bad : ℕ → Prop} {w w' : List Bool}
    (ha : agree bad w w') (v : Bool) : agree bad (w++[v]) (w'++[v]) := by
  obtain ⟨hl,hv⟩ := ha
  refine ⟨by simp [hl], fun i hi => ?_⟩
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (hl ▸ h)]
    exact hv i hi
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hl]

private theorem agree_run {bad : ℕ → Prop} (gs : List Gate) {w w' : List Bool}
    (ha : agree bad w w') (avoid : ∀ g ∈ gs, ∀ j ∈ g.inputs, ¬bad j) :
    agree bad (gs.foldl execGate w) (gs.foldl execGate w') := by
  induction gs generalizing w w' with
  | nil => exact ha
  | cons g gs ih =>
    have eq : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => ha.2 i (avoid g (by simp) i hi))
    apply ih
    · unfold execGate; rw [eq]; exact agree_append ha _
    · exact fun k hk => avoid k (by simp [hk])

private theorem run_original (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl execGate w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (execGate w g) (by simp [execGate]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem read_input {n} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by simp [List.getD_eq_getElem?_getD,i.isLt]

theorem swap_cherry {n : ℕ} (i j : Fin n) (pre post : List Gate) (op : GateOp)
    (hop : op = .and ∨ op = .or) (o : ℕ) (hoi : o ≠ i.val) (hoj : o ≠ j.val)
    (avoid : ∀ g ∈ pre ++ post, i.val ∉ g.inputs ∧ j.val ∉ g.inputs)
    (x : Fin n → Bool) :
    let C : Circuit := ⟨pre ++ ⟨op,[i.val,j.val]⟩ :: post,o⟩
    C.eval (List.ofFn (x ∘ Equiv.swap i j)) = C.eval (List.ofFn x) := by
  let y := x ∘ Equiv.swap i j
  let bad := fun k : ℕ => k=i.val ∨ k=j.val
  have a0 : agree bad (List.ofFn y) (List.ofFn x) := by
    refine ⟨by simp,fun k hk => ?_⟩
    by_cases hn : k<n
    · let v : Fin n := ⟨k,hn⟩
      change (List.ofFn y).getD v.val false = (List.ofFn x).getD v.val false
      rw [read_input,read_input]
      have hvi : v ≠ i := fun e => hk (Or.inl (congrArg Fin.val e))
      have hvj : v ≠ j := fun e => hk (Or.inr (congrArg Fin.val e))
      simp [y,Equiv.swap_apply_of_ne_of_ne hvi hvj]
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
  have skip (g : Gate) (hg : g ∈ pre ++ post) (k : ℕ) (hk : k ∈ g.inputs) : ¬bad k := by
    rintro (rfl | rfl)
    · exact (avoid g hg).1 hk
    · exact (avoid g hg).2 hk
  have apre := agree_run pre a0 (fun g hg => skip g (List.mem_append_left _ hg))
  let g : Gate := ⟨op,[i.val,j.val]⟩
  have value (z : Fin n → Bool) :
      g.op.eval (g.inputs.map fun k => (pre.foldl execGate (List.ofFn z)).getD k false) =
      op.eval [z i,z j] := by
    simp only [g,List.map_cons,List.map_nil]; rw [run_original,run_original,read_input,read_input] <;> simp
  have veq : op.eval [y i,y j] = op.eval [x i,x j] := by
    rcases hop with rfl|rfl <;> simp [y,GateOp.eval,Bool.and_comm,Bool.or_comm]
  have amid : agree bad (execGate (pre.foldl execGate (List.ofFn y)) g)
      (execGate (pre.foldl execGate (List.ofFn x)) g) := by
    change agree bad (_ ++ [_]) (_ ++ [_]); rw [value y,value x,veq]; exact agree_append apre _
  have afinal := agree_run post amid (fun g hg => skip g (List.mem_append_right _ hg))
  change ((pre ++ g :: post).foldl execGate (List.ofFn y)).getD o false =
    ((pre ++ g :: post).foldl execGate (List.ofFn x)).getD o false
  simp only [List.foldl_append,List.foldl_cons]
  exact afinal.2 o (by simp [bad,hoi,hoj])
end PEqualNP.Outside.L_meta_191_aux
namespace PEqualNP.Outside.L_meta_191_aux
open PEqualNP.CircuitLowerBounds

private theorem full_ports {gs : List Gate} (hl : (ports gs).length = 2*gs.length)
    (hb : ∀ g ∈ gs, g.inputs.length ≤ 2) : ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have h0 := hb g (by simp)
    have hb' := fun k (hk : k ∈ gs) => hb k (List.mem_cons_of_mem _ hk)
    have len := ports_length gs hb'
    change (g.inputs ++ ports gs).length = 2*(gs.length+1) at hl
    rw [List.length_append] at hl
    intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · omega
    · exact ih (by omega) hb' v hv

theorem ten_binary (gs : List Gate) (extra : ℕ)
    (he : (ports gs : Multiset ℕ) = Multiset.range 9 + {extra}) (hl : gs.length = 5)
    (hf : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ g ∈ gs, g.op = .not → g.inputs.length ≤ 1) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  have size := congrArg Multiset.card he
  simp only [Multiset.coe_card,Multiset.card_add,Multiset.card_range,Multiset.card_singleton] at size
  intro g hg
  have two := full_ports (gs:=gs) (by omega) (fun g h => (hf g h).2) g hg
  refine ⟨?_,two⟩
  rcases (hf g hg).1 with hand|hor|hnot
  · exact Or.inl hand
  · exact Or.inr hor
  · have := hn g hg hnot; omega

theorem extra_is_raw (C : Circuit) (extra : ℕ)
    (he : (ports C.gates : Multiset ℕ) = Multiset.range 9 + {extra}) (hl : C.gates.length = 5)
    (hbin : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (first : ∀ g, C.gates.head? = some g → ∀ v ∈ g.inputs, v < 5) (ho : 5 ≤ C.output)
    (asym : ∀ i j : Fin 5, i ≠ j → ∃ x, C.eval (List.ofFn (x ∘ Equiv.swap i j)) ≠ C.eval (List.ofFn x)) :
    extra < 5 := by
  by_contra! bad
  obtain ⟨gs,o⟩ := C
  change gs.length = 5 at hl
  cases gs with
  | nil => contradiction
  | cons g rest =>
    have hfirst : ∀ v ∈ g.inputs, v < 5 := first g rfl
    obtain ⟨hop,hins⟩ := hbin g (by simp)
    obtain ⟨op,ins⟩ := g
    cases ins with
    | nil => contradiction
    | cons a ins =>
      cases ins with
      | nil => simp at hins
      | cons b ins =>
        have empty : ins = [] := by simpa using hins
        subst ins
        have ha : a < 5 := hfirst a (by simp)
        have hb : b < 5 := hfirst b (by simp)
        change ((a :: b :: ports rest : List ℕ) : Multiset ℕ) = _ at he
        have counts (z : ℕ) (hz : z < 5) : (a::b::ports rest).count z = 1 := by
          have hh := congrArg (Multiset.count z) he
          have inc := Multiset.count_eq_one_of_mem (Multiset.nodup_range 9)
            (Multiset.mem_range.mpr (by omega : z < 9))
          have ne : z ≠ extra := by omega
          simpa only [Multiset.coe_count,Multiset.count_add,inc,Multiset.count_singleton,
            ite_eq_right ne,add_zero] using hh
        have ca := counts a ha
        have cb := counts b hb
        have ab : a ≠ b := by intro e; subst b; simp at ca
        have na : a ∉ ports rest := by
          intro hm
          have pos := List.count_pos_iff.mpr hm
          simp [Ne.symm ab] at ca; omega
        have nb : b ∉ ports rest := by
          intro hm
          have pos := List.count_pos_iff.mpr hm
          simp [ab] at cb; omega
        let i : Fin 5 := ⟨a,ha⟩
        let j : Fin 5 := ⟨b,hb⟩
        have neq : i ≠ j := fun ee => ab (congrArg Fin.val ee)
        obtain ⟨x,hx⟩ := asym i j neq
        apply hx
        apply swap_cherry i j [] rest op hop o (by change o ≠ a; change 5 ≤ o at ho; omega)
          (by change o ≠ b; change 5 ≤ o at ho; omega) _ x
        intro g hg
        simp only [List.nil_append] at hg
        exact ⟨fun h => na (List.mem_flatMap.mpr ⟨g,hg,h⟩),fun h => nb (List.mem_flatMap.mpr ⟨g,hg,h⟩)⟩
end PEqualNP.Outside.L_meta_191_aux

namespace PEqualNP.Outside.L_meta_191_aux
open CircuitLowerBounds

def base : List ℕ := [0,4294967295,2863311530,3435973836,4042322160,4278255360,4294901760]
def validOp (B : List ℕ) (v : ℕ) : Prop := v ∈ B ∨ (∃ a ∈ B, v = 4294967295 ^^^ a) ∨ ∃ a ∈ B, ∃ b ∈ B, v = a &&& b ∨ v = a ||| b

def maskInputs : List ℕ := [2863311530,3435973836,4042322160,4278255360,4294901760]

def row (x : Fin 5 → Bool) : ℕ :=
  (x 0).toNat + 2*(x 1).toNat + 4*(x 2).toNat + 8*(x 3).toNat + 16*(x 4).toNat

def readMask (x : Fin 5 → Bool) (m : ℕ) : Bool := m.testBit (row x)

private theorem maskInputs_eval : ∀ x : Fin 5 → Bool,
    maskInputs.map (readMask x) = List.ofFn x := by decide

private theorem ones_eval : ∀ x : Fin 5 → Bool, readMask x 4294967295 = true := by decide

private theorem zero_eval (x : Fin 5 → Bool) : readMask x 0 = false := by simp [readMask]

def gateMask (w : List ℕ) (g : Gate) : ℕ :=
  let ins := g.inputs.map fun i => w.getD i 0
  match g.op with
  | .and => match ins with | [] => 4294967295 | [a] => a | a::b::_ => a &&& b
  | .or => match ins with | [] => 0 | [a] => a | a::b::_ => a ||| b
  | .not => 4294967295 ^^^ ins.headD 0
  | _ => 0

def wireMasks (gs : List Gate) : List ℕ := gs.foldl (fun w g => w ++ [gateMask w g]) maskInputs

def admissible (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem mask_admissible {C : Circuit} (hc : MetaComplexity.FanInTwo C) :
    ∀ g ∈ C.gates, admissible g := fun g hg => hc g hg

theorem lookup_map (x : Fin 5 → Bool) (w : List ℕ) (i : ℕ) :
    (w.map (readMask x)).getD i false = readMask x (w.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [zero_eval]

private theorem gateMask_eval (x : Fin 5 → Bool) (w : List ℕ) (g : Gate) (hg : admissible g) :
    readMask x (gateMask w g) = g.op.eval (g.inputs.map fun i => (w.map (readMask x)).getD i false) := by
  obtain ⟨op,arity⟩ := hg
  obtain ⟨op', ins⟩ := g
  simp only at op arity
  simp_rw [lookup_map]
  have htop : (4294967295 : ℕ).testBit (row x) = true := ones_eval x
  rcases op with rfl | rfl | rfl <;> cases ins with
  | nil => simp [gateMask, GateOp.eval, readMask, htop]
  | cons a tail =>
    cases tail with
    | nil => simp [gateMask, GateOp.eval, readMask, Nat.testBit_and, Nat.testBit_or,
          Nat.testBit_xor, show (4294967295 : ℕ).testBit (row x) = true from ones_eval x]
    | cons b tail =>
      have ht : tail = [] := by simpa using arity
      subst tail
      simp [gateMask, GateOp.eval, readMask, Nat.testBit_and, Nat.testBit_or,
          Nat.testBit_xor, show (4294967295 : ℕ).testBit (row x) = true from ones_eval x]


theorem simulate (C : Circuit) (hf : MetaComplexity.FanInTwo C) (x : Fin 5 → Bool) :
    (wireMasks C.gates).map (readMask x) = C.wires (List.ofFn x) := by
  let step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  suffices H : ∀ (gs : List Gate) (w : List ℕ), (∀ g ∈ gs, admissible g) →
      (gs.foldl (fun ws g => ws ++ [gateMask ws g]) w).map (readMask x) =
      gs.foldl step (w.map (readMask x)) by
    simpa only [wireMasks, Circuit.wires, step, maskInputs_eval] using H C.gates maskInputs (mask_admissible hf)
  intro gs
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w h
    simp only [List.foldl_cons]
    rw [ih _ (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    simp [step, gateMask_eval x w g (h _ (by simp))]

theorem gateMask_valid (w B : List ℕ) (g : Gate) (hg : admissible g)
    (hsub : ∀ v ∈ w, v ∈ B) (hz : 0 ∈ B) (ho : 4294967295 ∈ B) :
    validOp B (gateMask w g) := by
  have input (i : ℕ) : w.getD i 0 ∈ B := by
    by_cases hi : i < w.length
    · simpa [List.getD_eq_getElem?_getD, hi] using hsub w[i] (List.getElem_mem hi)
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)] using hz
  obtain ⟨hop,arity⟩ := hg
  obtain ⟨op, ins⟩ := g
  simp only at hop arity
  rcases hop with rfl | rfl | rfl <;> cases ins with
  | nil => simp [gateMask, validOp, hz, ho]
  | cons a tail =>
    cases tail with
    | nil =>
      first | exact Or.inl (input a) | exact Or.inr (Or.inl ⟨_,input a,rfl⟩)
    | cons b tail =>
      first
      | exact Or.inr (Or.inr ⟨_,input a,_,input b,Or.inl rfl⟩)
      | exact Or.inr (Or.inr ⟨_,input a,_,input b,Or.inr rfl⟩)
      | exact Or.inr (Or.inl ⟨_,input a,rfl⟩)


theorem valid_bound {B : List ℕ} {v : ℕ} (hB : ∀ t ∈ B, t < 2^32) (h : validOp B v) :
    v < 2^32 := by
  rcases h with hv | ⟨a,ha,rfl⟩ | ⟨a,ha,b,hb,h|h⟩
  · exact hB _ hv
  · exact Nat.xor_lt_two_pow (by decide) (hB _ ha)
  · subst v
    exact Nat.and_lt_two_pow _ (hB _ hb)
  · subst v
    exact Nat.or_lt_two_pow (hB _ ha) (hB _ hb)

theorem wireMasks_bound (C : Circuit) (hf : MetaComplexity.FanInTwo C) :
    ∀ t ∈ wireMasks C.gates, t < 2^32 := by
  suffices aux : ∀ (gs : List Gate) (w : List ℕ), (∀ g ∈ gs, admissible g) →
      (∀ t ∈ w, t < 2^32) → ∀ t ∈ gs.foldl (fun ws g => ws ++ [gateMask ws g]) w, t < 2^32 by
    exact aux C.gates maskInputs (mask_admissible hf) (by decide)
  intro gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro w hg hw
    apply ih _ (fun t ht => hg t (by simp [ht]))
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hw t ht
    · obtain rfl : t = gateMask w g := by simpa using ht
      apply valid_bound (B := 0::4294967295::w)
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | rfl | ht
        · decide
        · decide
        · exact hw _ ht
      · exact gateMask_valid _ _ _ (hg _ (by simp)) (by simp_all) (by simp) (by simp)

theorem mask_inj {a b : ℕ} (ha : a < 2^32) (hb : b < 2^32)
    (h : ∀ x, readMask x a = readMask x b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 32
  · have hr : ∀ i : Fin 32, row (fun t => i.val.testBit t.val) = i.val := by decide
    have e := h (fun t : Fin 5 => j.testBit t.val)
    change a.testBit _ = b.testBit _ at e
    rwa [hr ⟨j,hj⟩] at e
  · have hp : 2^32 ≤ (2:ℕ)^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]

theorem wire_read (C : Circuit) (hf : MetaComplexity.FanInTwo C) (j : ℕ) (x : Fin 5 → Bool) :
    readMask x ((wireMasks C.gates).getD j 0) = (C.wires (List.ofFn x)).getD j false := by
  rw [← simulate C hf x, lookup_map]

theorem output_mask (C : Circuit) (hf : MetaComplexity.FanInTwo C)
    (hc : MetaComplexity.circuitFun 5 C = (fun x : Fin 5 → Bool =>
      decide (∃ i j : Fin 5, i.val+1=j.val ∧ x i=true ∧ x j=true))) :
    (wireMasks C.gates).getD C.output 0 = 4291360968 := by
  apply mask_inj
  · by_cases hi : C.output < (wireMasks C.gates).length
    · simpa [List.getD_eq_getElem?_getD, hi] using
        wireMasks_bound C hf _ (List.getElem_mem hi)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (wireMasks C.gates).length ≤ C.output)]
  · decide
  · intro x
    rw [wire_read C hf]
    change MetaComplexity.circuitFun 5 C x = _
    rw [hc]
    exact (by decide : ∀ y : Fin 5 → Bool,
      decide (∃ i j : Fin 5, i.val+1=j.val ∧ y i=true ∧ y j=true) = readMask y 4291360968) x


def path : List ℕ → List ℕ → Prop
  | _, [] => True
  | B, t::ts => validOp B t ∧ path (t::B) ts

def generated : List Gate → List ℕ → List ℕ
  | [], _ => []
  | g::gs, w => let t := gateMask w g; t :: generated gs (w ++ [t])

theorem generated_length (gs : List Gate) (w : List ℕ) :
    (generated gs w).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [generated, ih]

theorem generated_run (gs : List Gate) (w : List ℕ) :
    gs.foldl (fun ws g => ws ++ [gateMask ws g]) w = w ++ generated gs w := by
  induction gs generalizing w with
  | nil => simp [generated]
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [generated]

theorem generated_path (gs : List Gate) (w B : List ℕ)
    (hg : ∀ g ∈ gs, admissible g) (hw : ∀ t ∈ w, t ∈ B)
    (hz : 0 ∈ B) (ho : 4294967295 ∈ B) :
    path B (generated gs w) := by
  induction gs generalizing w B with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨gateMask_valid _ _ _ (hg _ (by simp)) hw hz ho, ih _ _ (by simp_all) ?_ (by simp [hz]) (by simp [ho])⟩
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact List.mem_cons_of_mem _ (hw _ ht)
    · simp_all

theorem path_pad {B xs : List ℕ} (hp : path B xs) (hz : 0 ∈ B) (k : ℕ) :
    path B (xs ++ List.replicate k 0) := by
  induction xs generalizing B with
  | nil =>
    simp only [List.nil_append]
    induction k generalizing B with
    | zero => trivial
    | succ k ih =>
      simp only [List.replicate_succ]
      exact ⟨Or.inl hz, ih (by trivial) (by simp)⟩
  | cons t ts ih =>
    exact ⟨hp.1, ih hp.2 (List.mem_cons_of_mem _ hz)⟩

theorem padded_path (C : Circuit) (hf : MetaComplexity.FanInTwo C) :
    path base (generated C.gates maskInputs ++ List.replicate (5-C.size) 0) := by
  apply path_pad _ (by decide)
  exact generated_path _ _ _ (mask_admissible hf) (by decide) (by decide) (by decide)

theorem output_generated (C : Circuit) (hf : MetaComplexity.FanInTwo C)
    (hc : MetaComplexity.circuitFun 5 C = (fun x : Fin 5 → Bool =>
      decide (∃ i j : Fin 5, i.val+1=j.val ∧ x i=true ∧ x j=true))) :
    4291360968 ∈ generated C.gates maskInputs := by
  have hout := output_mask C hf hc
  by_cases hi : C.output < (wireMasks C.gates).length
  · have hv : (wireMasks C.gates).getD C.output 0 ∈ wireMasks C.gates := by
      simpa [List.getD_eq_getElem?_getD, hi] using
        (List.getElem_mem hi : (wireMasks C.gates)[C.output] ∈ wireMasks C.gates)
    rw [hout] at hv
    rw [wireMasks, generated_run] at hv
    exact (List.mem_append.mp hv).resolve_left (by decide)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (wireMasks C.gates).length ≤ C.output)] at hout

theorem needed_generated (need : List ℕ) (nz : 0 ∉ need)
    (cert : ∀ a b c d e,
      validOp base a → validOp (a::base) b → validOp (b::a::base) c →
      validOp (c::b::a::base) d → validOp (d::c::b::a::base) e →
      4291360968 ∈ [e,d,c,b,a] → ∀ t ∈ need, t ∈ [e,d,c,b,a])
    (C : Circuit) (hf : MetaComplexity.FanInTwo C) (hl : C.size ≤ 5)
    (hc : MetaComplexity.circuitFun 5 C = (fun x : Fin 5 → Bool =>
      decide (∃ i j : Fin 5, i.val+1=j.val ∧ x i=true ∧ x j=true))) :
    ∀ t ∈ need, t ∈ generated C.gates maskInputs := by
  let xs := generated C.gates maskInputs
  let padded := xs ++ List.replicate (5-C.size) 0
  have hp : path base padded := padded_path C hf
  have ht : 4291360968 ∈ padded := List.mem_append_left _ (output_generated C hf hc)
  have hlp : padded.length = 5 := by
    simp only [padded,xs,List.length_append,generated_length,List.length_replicate]
    change C.size + (5-C.size) = 5
    omega
  have core (ys : List ℕ) (len : ys.length = 5) (p : path base ys) (target : 4291360968 ∈ ys) :
      ∀ t ∈ need, t ∈ ys := by
    obtain ⟨a,b,c,d,e,rfl⟩ : ∃ a b c d e, ys = [a,b,c,d,e] := by
      rcases ys with _ | ⟨a,ys⟩ <;> simp_all
      rcases ys with _ | ⟨b,ys⟩ <;> simp_all
      rcases ys with _ | ⟨c,ys⟩ <;> simp_all
      rcases ys with _ | ⟨d,ys⟩ <;> simp_all
      rcases ys with _ | ⟨e,ys⟩ <;> simp_all
    have hh := cert a b c d e p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 (by
      simpa [or_comm,or_left_comm,or_assoc] using target)
    intro t ht
    simpa [or_comm,or_left_comm,or_assoc] using hh t ht
  intro t hneed
  rcases List.mem_append.mp (core padded hlp hp ht t hneed) with h|h
  · exact h
  · exact False.elim (nz ((List.eq_of_mem_replicate h) ▸ hneed))

theorem exclude_not {need : List ℕ} (forbid : ∀ a ∈ 0::(maskInputs ++ need), 4294967295 ^^^ a ∉ need)
    (gs : List Gate) (w : List ℕ) (hw : ∀ a ∈ w, a ∈ maskInputs ++ need)
    (hg : ∀ t ∈ generated gs w, t ∈ need) : ∀ g ∈ gs, g.op ≠ .not := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    have first : gateMask w g ∈ need := hg _ (List.mem_cons_self ..)
    have go : g.op ≠ .not := by
      intro hn
      let a := (g.inputs.map fun i => w.getD i 0).headD 0
      have complement : gateMask w g = 4294967295 ^^^ a := by simp [gateMask, hn, a]
      apply forbid a _ (complement ▸ first)
      cases he : g.inputs with
      | nil => simp [a,he]
      | cons i ins =>
        by_cases hi : i < w.length
        · simpa [a, he, hi] using
            (List.mem_cons_of_mem 0 (hw _ (List.getElem_mem hi)))
        · simp [a,he,List.getElem?_eq_none (by omega : w.length ≤ i)]
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact go
    · apply ih (w ++ [gateMask w g]) _ _ t ht
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hw _ ha
        · obtain rfl : a = gateMask w g := by simpa using ha
          exact List.mem_append_right _ first
      · intro v hv
        exact hg _ (List.mem_cons_of_mem _ hv)

end PEqualNP.Outside.L_meta_191_aux
namespace PEqualNP.Outside.L_meta_191_aux
open CircuitLowerBounds
def targets191 : List ℕ := [4210752250,4294963440,3368601800,4278251520,4291360968]
def fns191 : List ((Fin 5 → Bool) → Bool) := [fun x => x 0 || x 2, fun x => x 2 || x 4, fun x => x 1 && (x 0 || x 2), fun x => x 3 && (x 2 || x 4), fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))]
theorem covers191 {ms : List ℕ} (hlen : ms.length ≤ 5)
    (h : ∀ t ∈ targets191, t ∈ ms) : ∀ t ∈ ms, t ∈ targets191 := by
  have hs : targets191.toFinset ⊆ ms.toFinset := by intro t ht; exact List.mem_toFinset.mpr (h t (List.mem_toFinset.mp ht))
  have hc : targets191.toFinset.card = 5 := by decide
  have he := Finset.eq_of_subset_of_card_le hs (by rw [hc]; exact ms.toFinset_card_le.trans hlen)
  intro t ht
  exact List.mem_toFinset.mp (he.symm.subset (List.mem_toFinset.mpr ht))
theorem fns191_eq : targets191.map (fun t x => readMask x t) = fns191 := by
  simp only [targets191, fns191, List.map_cons, List.map_nil, List.cons.injEq]
  repeat' constructor
  all_goals funext x; revert x; decide
theorem noComplement191 : ∀ t ∈ (base ++ targets191), 4294967295 ^^^ t ∉ targets191 := by decide
end PEqualNP.Outside.L_meta_191_aux
namespace PEqualNP.Outside.L_meta_191_aux
open CircuitLowerBounds
theorem wires191 (C : Circuit) (hf : MetaComplexity.FanInTwo C) (ms : List ℕ)
    (hw : wireMasks C.gates = maskInputs ++ ms) (hl : ms.length = 5)
    (hc : ∀ t ∈ targets191, t ∈ ms) :
    (∀ j < 5, ∃ f ∈ fns191, ∀ x, (C.wires (List.ofFn x)).getD (5+j) false = f x) ∧
    (∀ f ∈ fns191, ∃ j < 5, ∀ x, (C.wires (List.ofFn x)).getD (5+j) false = f x) := by
  have atj (j : ℕ) (hj : j < ms.length) (x : Fin 5 → Bool) :
      (C.wires (List.ofFn x)).getD (5+j) false = readMask x ms[j] := by
    rw [← wire_read C hf, hw, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [maskInputs])]
    simp [maskInputs, List.getElem?_eq_getElem hj]
  rw [← fns191_eq]
  constructor
  · intro j hj
    have hlt : j < ms.length := hl ▸ hj
    exact ⟨_, List.mem_map.mpr ⟨ms[j], covers191 hl.le hc _ (List.getElem_mem hlt), rfl⟩, atj j hlt⟩
  · intro f hf'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf'
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (hc t ht)
    exact ⟨j, hl ▸ hj, fun x => (atj j hj x).trans (congrArg (readMask x) he)⟩
end PEqualNP.Outside.L_meta_191_aux
namespace PEqualNP.Outside.L_meta_191_aux
open CircuitLowerBounds

private def outputs191 (w : List ℕ) : List Gate → List ℕ
  | [] => []
  | g :: gs => gateMask w g :: outputs191 (w ++ [gateMask w g]) gs

private theorem fold_outputs191 (gs : List Gate) (w : List ℕ) :
    gs.foldl (fun ws g => ws ++ [gateMask ws g]) w = w ++ outputs191 w gs := by
  induction gs generalizing w with
  | nil => simp [outputs191]
  | cons g gs ih => simp [outputs191, ih, List.append_assoc]

theorem noNot191 (gs : List Gate)
    (hall : ∀ t ∈ (wireMasks gs).drop maskInputs.length, t ∈ targets191) :
    ∀ g ∈ gs, g.op ≠ .not := by
  have aux (ls : List Gate) (w : List ℕ)
      (hw : ∀ t ∈ w, t ∈ base ++ targets191)
      (hout : ∀ t ∈ outputs191 w ls, t ∈ targets191) :
      ∀ g ∈ ls, g.op ≠ .not := by
    induction ls generalizing w with
    | nil => simp
    | cons g ls ih =>
      have hg := hout (gateMask w g) (by simp [outputs191])
      intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · intro hn
        have hz : 0 ∈ base ++ targets191 := by decide
        have hi (i : ℕ) : w.getD i 0 ∈ base ++ targets191 := by
          by_cases ha : i < w.length
          · simpa [List.getD_eq_getElem?_getD, ha] using hw w[i] (List.getElem_mem ha)
          · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)] using hz
        rw [gateMask, hn] at hg
        cases hgins : h.inputs with
        | nil => exact noComplement191 _ hz (by simpa [hgins] using hg)
        | cons i is => exact noComplement191 _ (hi i) (by simpa [hgins] using hg)
      · apply ih (w ++ [gateMask w g]) _ _ h hh
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact hw t ht
          · obtain rfl : t = gateMask w g := by simpa using ht
            exact List.mem_append_right _ hg
        · intro t ht
          exact hout t (List.mem_cons_of_mem _ ht)
  apply aux gs maskInputs (by decide)
  simpa [wireMasks, fold_outputs191] using hall

end PEqualNP.Outside.L_meta_191_aux
namespace PEqualNP.Outside.L_meta_191_aux
open CircuitLowerBounds MetaComplexity PEqualNP.Outside
theorem all_ports191 (D : Circuit) (hm : IsMinimalCircuit 5 D)
    (hc : circuitFun 5 D = Read191.path) (hl : D.gates.length = 5) :
    ∀ i < 9, i ∈ ports D.gates := by
  have ho := Read191.last_output D hm (by omega)
  intro i hi
  apply List.mem_flatMap.mpr
  by_cases hr : i < 5
  · obtain ⟨g,hg,hh⟩ := Read191.path_reads D hc ⟨i,hr⟩
    refine ⟨g,hg,?_⟩
    rcases g with ⟨op,ins⟩
    cases op <;> simp_all [Read191.active]
    exact List.mem_of_mem_take hh
  · obtain ⟨q,_,hq⟩ := Live191.live D hm (i-5) (by omega) (by omega)
    exact ⟨_,List.get_mem _ _,by simpa [show 5+(i-5)=i by omega] using hq⟩
theorem mask_ext191 (C D : Circuit) (hc : FanInTwo C) (hd : FanInTwo D)
    (hl : C.gates.length = D.gates.length)
    (hw : ∀ x : Fin 5 → Bool, C.wires (List.ofFn x) = D.wires (List.ofFn x)) :
    wireMasks C.gates = wireMasks D.gates := by
  apply List.ext_getElem
  · simp [wireMasks,generated_run,generated_length,hl]
  · intro i h₁ h₂
    apply mask_inj (wireMasks_bound C hc _ (List.getElem_mem h₁)) (wireMasks_bound D hd _ (List.getElem_mem h₂))
    intro x
    have h := (wire_read C hc i x).trans ((congrArg (fun w : List Bool => w.getD i false) (hw x)).trans (wire_read D hd i x).symm)
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h₁,List.getElem?_eq_getElem h₂, Option.getD_some] using h
theorem finish191 (C : Circuit) (hm : IsMinimalCircuit 5 C) (hl : C.gates.length = 5)
    (hc : ∀ t ∈ targets191, t ∈ (wireMasks C.gates).drop 5) :
    (∀ g ∈ C.gates, g.op ≠ .not) ∧
    (∀ j < 5, ∃ f ∈ fns191, ∀ x, (C.wires (List.ofFn x)).getD (5+j) false = f x) ∧
    (∀ f ∈ fns191, ∃ j < 5, ∀ x, (C.wires (List.ofFn x)).getD (5+j) false = f x) := by
  let ms := generated C.gates maskInputs
  have hw : wireMasks C.gates = maskInputs ++ ms := generated_run _ _
  have hlen : ms.length = 5 := (generated_length ..).trans hl
  have hd : (wireMasks C.gates).drop 5 = ms := by rw [hw]; simp [maskInputs]
  rw [hd] at hc
  refine ⟨noNot191 _ ?_,wires191 C hm.1 ms hw hlen hc⟩
  change ∀ t ∈ (wireMasks C.gates).drop 5, _
  rw [hd]
  exact covers191 hlen.le hc
end PEqualNP.Outside.L_meta_191_aux

namespace PEqualNP.Outside.Split191

def path5 (x : Fin 5 → Bool) := decide (∃ i j : Fin 5, i.val+1=j.val ∧ x i=true ∧ x j=true)

def mix (S : Finset (Fin 5)) (a b : Fin 5 → Bool) (i : Fin 5) := if i ∈ S then a i else b i

private def index (S : Finset (Fin 5)) : ℕ := ∑ i ∈ S, 2^i.val

-- Six 5-bit assignments per subset: three rows and a column separating each pair.
private def witnesses : Array ℕ := #[0, 0, 0, 134208, 0, 270602272, 41979968, 8392800, 0, 71376928, 37789760, 134208, 83959936, 83959840, 38976, 16785504, 0, 75579424, 41992256, 134208, 75579520, 270602272, 41979968, 8392800, 155904, 71376928, 37789760, 134208, 77952, 77856, 38976, 0]

private def assignment (S : Finset (Fin 5)) (k : ℕ) (i : Fin 5) :=
  (witnesses[index S]?.getD 0).testBit (5*k+i.val)

private theorem separated : ∀ S : Finset (Fin 5), 2 ≤ S.card → S.card ≤ 4 →
    path5 (mix S (assignment S 0) (assignment S 3)) ≠ path5 (mix S (assignment S 1) (assignment S 3)) ∧
    path5 (mix S (assignment S 0) (assignment S 4)) ≠ path5 (mix S (assignment S 2) (assignment S 4)) ∧
    path5 (mix S (assignment S 1) (assignment S 5)) ≠ path5 (mix S (assignment S 2) (assignment S 5)) := by decide

theorem no_summary (S : Finset (Fin 5)) (h₂ : 2 ≤ S.card) (h₄ : S.card ≤ 4)
    (encode : (Fin 5 → Bool) → Bool) (decode : Bool → (Fin 5 → Bool) → Bool) :
    ¬ ∀ a b, path5 (mix S a b) = decode (encode a) b := by
  intro he
  obtain ⟨p,q,r⟩ := separated S h₂ h₄
  simp only [he] at p q r
  cases h₀ : encode (assignment S 0) <;>
    cases h₁ : encode (assignment S 1) <;>
    cases h₂' : encode (assignment S 2) <;> simp_all

theorem no_transposition : ∀ i j : Fin 5, i ≠ j → ∃ x : Fin 5 → Bool,
    path5 (x ∘ Equiv.swap i j) ≠ path5 x := by decide

end PEqualNP.Outside.Split191
namespace PEqualNP.Outside.L_meta_191_aux
open CircuitLowerBounds MetaComplexity PEqualNP.Outside
theorem through_ports (D : Circuit) (hm : IsMinimalCircuit 5 D) (hc : circuitFun 5 D = Read191.path)
    (hl : D.gates.length = 5) (hgood : ∀ i g, D.gates[i]? = some g → Tidy191.good (5+i) g)
    (h9 : (ports D.gates : Multiset ℕ) = Multiset.range 9 → False)
    (h10 : ∀ extra, extra < 5 → (ports D.gates : Multiset ℕ) = Multiset.range 9 + {extra} →
      (∀ g ∈ D.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
      (wireMasks D.gates).getD 9 0 = 4291360968 →
      ∀ t ∈ targets191, t ∈ (wireMasks D.gates).drop 5) :
    ∀ t ∈ targets191, t ∈ (wireMasks D.gates).drop 5 := by
  obtain h | ⟨extra,he⟩ := ports_cases D.gates hl.le (fun g hg => (hm.1 g hg).2) (all_ports191 D hm hc hl)
  · exact (h9 h).elim
  have hnot (g) (hg : g ∈ D.gates) : g.op = .not → g.inputs.length ≤ 1 := by
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
    exact (hgood i g hi).2.2
  have hb := ten_binary D.gates extra he hl hm.1 hnot
  have first (g : Gate) (hg : D.gates.head? = some g) := (hgood 0 g (by simpa only [List.head?_eq_getElem?] using hg)).2.1
  have ho := Read191.last_output D hm (by omega)
  have hn : D.output = 9 := by omega
  have hr := extra_is_raw D extra he hl hb (by simpa using first) (by omega) (by
    intro i j hij
    obtain ⟨x,hx⟩ := Split191.no_transposition i j hij
    use x
    change circuitFun 5 D _ ≠ circuitFun 5 D _
    simpa only [← hc] using (show Read191.path (x ∘ Equiv.swap i j) ≠ Read191.path x from hx))
  apply h10 extra hr he hb
  rw [← hn]
  exact output_mask D hm.1 hc
end PEqualNP.Outside.L_meta_191_aux

open PEqualNP.MetaComplexity

-- Reuses project proofs at 3ec921591ffc6536fad46069ec0c219464fb6ffc.

-- Adapted from PEqualNP.MetaComplexity.Helpers.Shannon in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib

open PEqualNP.CircuitLowerBounds

 
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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

 

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

 
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.Outside.L_meta_191_PathLib

-- Adapted from PEqualNP.MetaComplexity.Helpers.Support in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

 
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

 
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

 
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

 

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

 
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

 

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.Outside.L_meta_191_PathLib

-- Adapted from PEqualNP.MetaComplexity.Helpers.Elim in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib

open PEqualNP.CircuitLowerBounds

 
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

 
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

 
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

 

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

 
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

 

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

 

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

 

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

 
theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

 

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_191_PathLib

-- Adapted from PEqualNP.MetaComplexity.Helpers.Parity in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib

open PEqualNP.CircuitLowerBounds

 

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

 

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

 
theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

 
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

 

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

 

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

 

 

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

 

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

 

 
def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

 
theorem par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega

 
theorem parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega

end PEqualNP.Outside.L_meta_191_PathLib

-- Adapted from PEqualNP.MetaComplexity.Helpers.Parity3 in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib

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

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

 
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

 
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

 
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

 
theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

 

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

 

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

 
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

 

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

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

 

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

 

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

 

 

theorem supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj

 

theorem exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep

 
theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

 

 
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

theorem three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount

 

theorem three_core (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (g0 : Gate) (h0 : gs[0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c) ∨
      ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1) = Stat.const c0 :=
    hrd (fixBit g0) 0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b 0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ 0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
  
  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ 0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩

 
theorem stat_first (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b (n + 1) = (simplify g0.op n
      (g0.inputs.map fun a => (statAt n i b).getD a (Stat.const false))).2 := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  show (elim n ([] ++ g0 :: post) (statAt n i b, [])).1.getD (n + 1) (Stat.const false) = _
  rw [elim_split_getD n [] g0 post _ (n + 1) _ (by
    show n + 1 ≤ (statAt n i b).length + 0
    rw [statAt_length])]
  exact getD_snoc_len (statAt n i b) _ _ _ (statAt_length n i b)

 
theorem first_any (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1))
    (hshape : (g0.op = GateOp.not ∧ g0.inputs = [(i : ℕ)]) ∨
      ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs = [(i : ℕ), (i : ℕ)])) :
    ∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c := by
  intro c
  rcases hshape with ⟨hop, hin⟩ | ⟨hop | hop, hin⟩
  · refine ⟨!c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpNot]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpAnd]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpOr]

 

theorem single_reader (n : ℕ) (gs : List Gate) (o : ℕ) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i k : Fin (n + 1)) (hik : k ≠ i) (hop : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hin : g0.inputs = [(i : ℕ), (k : ℕ)]) (hoi : o ≠ i)
    (hno : ∀ p' g', gs[p']? = some g' → p' ≠ 0 → (i : ℕ) ∉ g'.inputs)
    (hdep : ∀ u : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false) : False := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
    intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno (q + 1) g (by simpa using hq) (by omega)
  let u : Fin (n + 1) → Bool := fun j => if j = k then fixBit g0 else false
  have huk : u k = fixBit g0 := by simp [u]
  have hu'k : Function.update u i (!u i) k = fixBit g0 := by
    rw [Function.update_of_ne hik]; exact huk
  apply hdep u
  show (wiresFrom post (List.ofFn (Function.update u i (!u i)) ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn (Function.update u i (!u i))).getD a false)])).getD
        o false
    = (wiresFrom post (List.ofFn u ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn u).getD a false)])).getD o false
  apply agree_except i post _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjl : j = n + 1
  · rw [hjl, getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hin]
    simp only [List.map_cons, List.map_nil, getD_ofFn, huk, hu'k]
    rcases hop with hop | hop
    · have hf : fixBit g0 = false := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
    · have hf : fixBit g0 = true := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
  · rw [getD_snoc_ne _ _ _ _ (by simpa using hjl), getD_snoc_ne _ _ _ _ (by simpa using hjl)]
    by_cases hlt : j < n + 1
    · have e1 : (List.ofFn (Function.update u i (!u i))).getD j false
          = Function.update u i (!u i) ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      have e2 : (List.ofFn u).getD j false = u ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      rw [e1, e2]
      exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

 

theorem three_saved (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c) :
    ∃ (i : Fin (n + 1)) (b : Bool),
      (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    by_contra hns
    refine hdep i (fun _ => false) ?_
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
  have hoi : ∀ i : Fin (n + 1), o ≠ i :=
    fun i e => hout i false false (by rw [e]; exact stF_self n gs i false)
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := exists_reader (n + 1) 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        [] o (hoi 0) (hsupp 0)
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
      (by rw [hin]; exact List.mem_cons_self)
      (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inl ⟨hop, hin⟩)))
    exact ⟨⟨j, hj⟩, b, hb⟩
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
        (by rw [hin]; exact List.mem_cons_self)
        (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inr ⟨hop, hin⟩)))
      exact ⟨⟨j, hj⟩, b, hb⟩
    · by_cases hr : ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ j ∈ g'.inputs
      · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
          (by rw [hin]; exact List.mem_cons_self) (Or.inr hr)
        exact ⟨⟨j, hj⟩, b, hb⟩
      · exfalso
        exact single_reader n gs o g0 h0 ⟨j, hj⟩ ⟨k, hk⟩
          (fun e => hjk (congrArg Fin.val e).symm) hop hin (hoi ⟨j, hj⟩)
          (fun p' g' hp' hp0 hx => hr ⟨p', g', hp0, hp', hx⟩) (hdep ⟨j, hj⟩)

 

theorem par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this

 

theorem clean_step (n : ℕ) (c : Bool) (s : ℕ)
    (h : HasClean (n + 1 + 1) (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) s) :
    ∃ (c' : Bool) (s' : ℕ), s' + 3 ≤ s ∧
      HasClean (n + 1) (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) c') s' := by
  obtain ⟨gs, o, hcl, hsz, hev⟩ := h
  have hev' : ∀ x : Fin (n + 1 + 1) → Bool,
      (wiresFrom gs (List.ofFn x)).getD o false = xor (par (n + 1 + 1) x) c := hev
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have hinv : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      Inv (n + 1) (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.insertNth i b y : Fin (n + 1 + 1) → Bool)))
        (elim (n + 1) gs (statAt (n + 1) i b, [])) :=
    fun i b y => inv_elim (n + 1) _ (by simp) gs _ _ hok (inv_at (n + 1) i b y)
  have hval : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      (stF (n + 1) gs i b o).val (wiresFrom (elim (n + 1) gs (statAt (n + 1) i b, [])).2
        (List.ofFn y)) = xor (par (n + 1) y) (xor b c) := by
    intro i b y
    have := ((hinv i b y).2 o).2
    rw [hev', par_insertNth, Bool.xor_assoc] at this
    exact this
  have hout : ∀ (i : Fin (n + 1 + 1)) (b c' : Bool), stF (n + 1) gs i b o ≠ Stat.const c' := by
    intro i b c' hst
    have h1 := hval i b (Fin.snoc (fun _ => false) false)
    have h2 := hval i b (Fin.snoc (fun _ => false) true)
    rw [hst] at h1 h2
    have e := h1.symm.trans h2
    rw [par_snoc, par_snoc] at e
    revert e
    cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
  have hdep : ∀ (i : Fin (n + 1 + 1)) (u : Fin (n + 1 + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false := by
    intro i u
    rw [hev', hev', par_flip]
    cases par (n + 1 + 1) u <;> cases c <;> simp
  obtain ⟨i, b, hb⟩ := three_saved (n + 1) gs hcl o hdep hout
  cases hst : stF (n + 1) gs i b o with
  | const c' => exact absurd hst (hout i b c')
  | wire j =>
    refine ⟨xor b c, (elim (n + 1) gs (statAt (n + 1) i b, [])).2.length, by omega,
      (elim (n + 1) gs (statAt (n + 1) i b, [])).2, j, ?_, le_refl _, ?_⟩
    · exact clean_elim (n + 1) (List.ofFn fun _ : Fin (n + 1) => false) (by simp) gs _ _ hok
        (inv_at (n + 1) i b _) (by intro p g hp; simp at hp)
    · intro y
      have := hval i b y
      rw [hst] at this
      exact this

 
theorem par_lower3 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    obtain ⟨c', s', hs, h'⟩ := clean_step n c s h
    have := ih c' s' h'
    omega

 
theorem parity_lower3 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    3 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower3 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.Outside.L_meta_191_PathLib

-- Adapted from PEqualNP.MetaComplexity.Helpers.Parity4 in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib

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

 
theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

 

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

 
theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

 

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

 
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

 
theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

 

 
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

 
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

 
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Stat.wire k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k

 
theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Stat.const c) :
    (simplify g.op t (g.inputs.map F)).2 = Stat.wire t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpOr, hF, hF']

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

 
theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Stat.const c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Stat.wire q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

 

theorem st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Stat.const c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Stat.const c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'

theorem four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount

 

 
def Red (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (i : Fin (n + 1)) (b : Bool) (gs' : List Gate) (o' : ℕ), CleanL n gs' ∧
    gs'.length + 4 ≤ gs.length ∧ ∀ y : Fin n → Bool, vl gs' y o' = vl gs (ins i b y) o

 

structure Min (n : ℕ) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL (n + 1) gs
  hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
    vl gs (Function.update u i (!u i)) o ≠ vl gs u o
  hnc : ∀ (i : Fin (n + 1)) (b : Bool), ∃ y y' : Fin n → Bool,
    vl gs (ins i b y) o ≠ vl gs (ins i b y') o
  m1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = c
  m2 : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
    ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = vl gs u j
  nored : ¬ Red n gs o

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

theorem Min.out (M : Min n gs o) (i : Fin (n + 1)) (b c : Bool) :
    stF n gs i b o ≠ Stat.const c := by
  intro h
  obtain ⟨y, y', hne⟩ := M.hnc i b
  exact hne ((st_val_const n gs M.hcl i b o c h y).trans
    (st_val_const n gs M.hcl i b o c h y').symm)

theorem Min.pass (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) :
    ∃ j, CleanL n (passG n gs i b) ∧
      ∀ y : Fin n → Bool, vl (passG n gs i b) y j = vl gs (ins i b y) o := by
  cases hst : stF n gs i b o with
  | const c => exact absurd hst (M.out i b c)
  | wire j =>
    refine ⟨j, ?_, fun y => (st_val_wire n gs M.hcl i b o j hst y).symm⟩
    exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (fun g hg => (clean_nok _ gs M.hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)

theorem Min.nf4 (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    False := by
  obtain ⟨j, hc, he⟩ := M.pass i b
  exact M.nored ⟨i, b, _, j, hc,
    four_count n gs M.hcl i b p1 p2 p3 p4 h12 h13 h14 h23 h24 h34 h1 h2 h3 h4, he⟩

 

theorem Min.ndup (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2)
    (h3 : RC n gs i b p3) (p j q k : ℕ) (hq : stF n gs i b p = Stat.wire q) (hnq : n ≤ q)
    (hk : stF n gs i b j = Stat.wire k) (hkq : k < q)
    (heq : ∀ y : Fin n → Bool, vl gs (ins i b y) p = vl gs (ins i b y) j) : False := by
  obtain ⟨jo, hc, he⟩ := M.pass i b
  have h3c : (passG n gs i b).length + 3 ≤ gs.length :=
    three_count n gs M.hcl i b p1 p2 p3 h12 h13 h23 h1 h2 h3
  have hqv : q < n + (passG n gs i b).length := by
    have h := ((inv_stF n gs M.hcl i b (fun _ => false)).2 p).1
    rw [show (elim n gs (statAt n i b, [])).1.getD p (Stat.const false) = Stat.wire q from hq]
      at h
    exact h
  have heq1 : ∀ y : Fin n → Bool,
      vl (passG n gs i b) y (n + (q - n)) = vl (passG n gs i b) y k := by
    intro y
    rw [show n + (q - n) = q by omega, ← st_val_wire n gs M.hcl i b p q hq y,
      ← st_val_wire n gs M.hcl i b j k hk y]
    exact heq y
  obtain ⟨y, y', hne⟩ := M.hnc i b
  obtain ⟨gs2, o2, hc2, hl2, he2⟩ := drop_alias n (passG n gs i b) hc jo (q - n) k (by omega)
    (by omega) heq1 ⟨y, y', by rw [he y, he y']; exact hne⟩
  exact M.nored ⟨i, b, gs2, o2, hc2, by omega, fun y => by rw [he2 y, he y]⟩

theorem Min.reader (M : Min n gs o) (i : Fin (n + 1)) (B : ℕ → Prop) (hi : B i) (ho : ¬ B o) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (n + 1 + p) ∧ ∃ a ∈ g.inputs, B a := by
  apply exists_reader (n + 1) i B hi gs o ho
  by_contra hns
  refine M.hdep i (fun _ => false) ?_
  exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ i := fun e => hns (e ▸ hk)
      simp [Function.update_of_ne this])

 

theorem Min.cb (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (B : ℕ → Prop) (hi : B i)
    (hB : ∀ a, B a → IsC n gs i b a) :
    ∃ h1 h2, h1 ≠ h2 ∧ ¬ B (n + 1 + h1) ∧ ¬ B (n + 1 + h2) ∧ RC n gs i b h1 ∧ RC n gs i b h2 := by
  have ho : ¬ B o := fun h => by
    obtain ⟨c, hc⟩ := hB o h
    exact M.out i b c hc
  obtain ⟨h1, g1, hg1, hB1, a1, ha1, hBa1⟩ := M.reader i B hi ho
  have r1 : RC n gs i b h1 := ⟨g1, hg1, a1, ha1, hB a1 hBa1⟩
  by_cases hex : ∃ h2 g2, h2 ≠ h1 ∧ gs[h2]? = some g2 ∧ ¬ B (n + 1 + h2) ∧ ∃ a ∈ g2.inputs, B a
  · obtain ⟨h2, g2, hne, hg2, hB2, a2, ha2, hBa2⟩ := hex
    exact ⟨h1, h2, Ne.symm hne, hB1, hB2, r1, ⟨g2, hg2, a2, ha2, hB a2 hBa2⟩⟩
  by_cases hc1 : IsC n gs i b (n + 1 + h1)
  · obtain ⟨h2, g2, hg2, hB2, a2, ha2, hBa2⟩ := M.reader i (fun a => B a ∨ a = n + 1 + h1)
      (Or.inl hi) (fun h => h.elim ho (fun e => by
        obtain ⟨c, hc⟩ := hc1
        exact M.out i b c (by rw [e]; exact hc)))
    have hB2' : ¬ (B (n + 1 + h2) ∨ n + 1 + h2 = n + 1 + h1) := hB2
    have hBa2' : B a2 ∨ a2 = n + 1 + h1 := hBa2
    refine ⟨h1, h2, fun e => hB2' (Or.inr (by rw [e])), hB1, fun h => hB2' (Or.inl h), r1,
      g2, hg2, a2, ha2, ?_⟩
    rcases hBa2' with h | h
    · exact hB a2 h
    · rw [h]; exact hc1
  · exfalso
    obtain ⟨c1, hc1'⟩ := hB a1 hBa1
    obtain ⟨hop, _, w, hw, hwn⟩ := st_shape n gs M.hcl i b h1 g1 hg1 a1 ha1 c1 hc1'
      (fun c' h => hc1 ⟨c', h⟩)
    have hBw : ¬ B w := fun h => by
      obtain ⟨c, hc⟩ := hB w h
      exact hwn c hc
    have hwlt : w < n + 1 + h1 := (M.hcl h1 g1 hg1).lt w hw
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    obtain ⟨u, hu⟩ := takes gs M.m1 w (by omega) (fixBit g1)
    apply M.hdep i u
    refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
    · intro j hj hBj
      rw [vl_input gs _ j hj, vl_input gs _ j hj]
      exact Function.update_of_ne
        (fun e => hBj (by rw [show j = (i : ℕ) from congrArg Fin.val e]; exact hi)) _ _
    · intro p g hp _ hBp hr hear
      obtain ⟨a, ha, hBa⟩ := hr
      have hp1 : p = h1 := by
        by_contra hne
        exact hex ⟨p, g, hne, hp, hBp, a, ha, hBa⟩
      rw [hp1] at hear ⊢
      rw [vl_abs gs M.hcl _ h1 g1 hg1 hop w hw (by rw [hear w hwlt hBw]; exact hu),
        vl_abs gs M.hcl u h1 g1 hg1 hop w hw hu]

 
theorem Min.one_const (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p q : ℕ) (hpq : p ≠ q)
    (gp gq : Gate) (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (cp : IsC n gs i b (n + 1 + p)) (cq : IsC n gs i b (n + 1 + q)) : False := by
  obtain ⟨h1, h2, h12, hB1, hB2, r1, r2⟩ := M.cb i b
    (fun a => a = (i : ℕ) ∨ a = n + 1 + p ∨ a = n + 1 + q) (Or.inl rfl) (by
      intro a ha
      rcases ha with e | e | e
      · rw [e]; exact ⟨b, stF_self n gs i b⟩
      · rw [e]; exact cp
      · rw [e]; exact cq)
  have hB1' : ¬ (n + 1 + h1 = (i : ℕ) ∨ n + 1 + h1 = n + 1 + p ∨ n + 1 + h1 = n + 1 + q) := hB1
  have hB2' : ¬ (n + 1 + h2 = (i : ℕ) ∨ n + 1 + h2 = n + 1 + p ∨ n + 1 + h2 = n + 1 + q) := hB2
  exact M.nf4 i b p q h1 h2 hpq (fun e => hB1' (Or.inr (Or.inl (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inl (by rw [e])))) (fun e => hB1' (Or.inr (Or.inr (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inr (by rw [e])))) h12
    (rc_of_const n gs M.hcl i b p gp hp cp) (rc_of_const n gs M.hcl i b q gq hq cq) r1 r2

theorem Min.reader_const (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hr : (i : ℕ) ∈ g.inputs) : IsC n gs i (fixBit g) (n + 1 + p) :=
  const_read n gs M.hcl i _ p g hp i hr (stF_self n gs i _)

 
theorem Min.no_not (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.not) (hr : (i : ℕ) ∈ g.inputs) : False := by
  have hin : g.inputs = [(i : ℕ)] := by
    rcases M.hcl p g hp with ⟨_, j, _, hin⟩ | ⟨h, _⟩
    · rw [hin] at hr
      have e : (i : ℕ) = j := by simpa using hr
      rw [hin, e]
    · rcases h with h | h <;> rw [hop] at h <;> cases h
  have hN : ∀ b, IsC n gs i b (n + 1 + p) := fun b =>
    st_allconst n gs M.hcl i b p g hp (fun a ha => by
      rw [hin] at ha
      have e : a = (i : ℕ) := by simpa using ha
      rw [e]; exact ⟨b, stF_self n gs i b⟩)
  have hNv : ∀ b, stF n gs i b (n + 1 + p) = Stat.const (!b) := by
    intro b
    obtain ⟨c, hc⟩ := hN b
    have h1 := st_val_const n gs M.hcl i b (n + 1 + p) c hc (fun _ => false)
    have h2 : vl gs (ins i b fun _ => false) (i : ℕ) = b := by
      rw [vl_input gs _ i i.isLt]; simp [ins]
    have h3 : c = !b := by
      rw [← h1, vl_gate gs M.hcl _ p g hp, hop, hin]
      simp [GateOp.eval, h2]
    rw [hc, h3]
  have ho : ¬ (o = (i : ℕ) ∨ o = n + 1 + p) := by
    intro h
    rcases h with e | e
    · exact M.out i false false (by rw [e]; exact stF_self n gs i false)
    · exact M.out i false _ (by rw [e]; exact hNv false)
  obtain ⟨q, gq, hq, hBq, a, ha, hBa⟩ :=
    M.reader i (fun a => a = (i : ℕ) ∨ a = n + 1 + p) (Or.inl rfl) ho
  have hBq' : ¬ (n + 1 + q = (i : ℕ) ∨ n + 1 + q = n + 1 + p) := hBq
  have hBa' : a = (i : ℕ) ∨ a = n + 1 + p := hBa
  have hpq : p ≠ q := fun e => hBq' (Or.inr (by rw [e]))
  have hcq : ∃ b, IsC n gs i b (n + 1 + q) := by
    rcases hBa' with e | e
    · exact ⟨fixBit gq, M.reader_const i q gq hq (e ▸ ha)⟩
    · refine ⟨!fixBit gq, const_read n gs M.hcl i _ q gq hq (n + 1 + p) (e ▸ ha) ?_⟩
      rw [hNv]; simp
  obtain ⟨b0, hb0⟩ := hcq
  exact M.one_const i b0 p q hpq g gq hp hq (hN b0) hb0

 

theorem Min.forced (M : Min n gs o) (X : Fin (n + 1)) (p q : ℕ) (gp : Gate)
    (hp : gs[p]? = some gp) (hXp : (X : ℕ) ∈ gp.inputs)
    (hR : ∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = p ∨ p' = q)
    (hqo : o ≠ n + 1 + q) (u : Fin (n + 1) → Bool)
    (hq : vl gs (Function.update u X (!u X)) (n + 1 + q) = vl gs u (n + 1 + q) ∨
      ∀ (p' : ℕ) (g' : Gate), gs[p']? = some g' → (n + 1 + q) ∉ g'.inputs) :
    vl gs u (n + 1 + p) = u X := by
  by_contra hne
  have hX : vl gs u X = u X := vl_input gs u X X.isLt
  have hX' : vl gs (Function.update u X (!u X)) X = !u X := by
    rw [vl_input gs _ X X.isLt]; simp
  have key : vl gs (Function.update u X (!u X)) (n + 1 + p) = vl gs u (n + 1 + p) := by
    rcases M.hcl p gp hp with ⟨hopn, _⟩ | ⟨hop, j, k, _, _, hin⟩
    · exact (M.no_not X p gp hp hopn hXp).elim
    · have e1 : ∀ v : Fin (n + 1) → Bool,
          vl gs v (n + 1 + p) = gp.op.eval [vl gs v j, vl gs v k] := by
        intro v
        rw [vl_gate gs M.hcl v p gp hp, hin]
        rfl
      rw [e1 u] at hne
      rw [e1 u, e1 (Function.update u X (!u X))]
      have hjk : (X : ℕ) = j ∨ (X : ℕ) = k := by rw [hin] at hXp; simpa using hXp
      rcases hjk with e | e
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) k = w'
        generalize vl gs u k = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) j = w'
        generalize vl gs u j = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
  apply M.hdep X u
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ) ∨ a = n + 1 + q) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ) ∨ j = n + 1 + q) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (Or.inl (congrArg Fin.val e))) _ _
  · intro p' g' hp' _ hB' hr hear
    have hB'' : ¬ (n + 1 + p' = (X : ℕ) ∨ n + 1 + p' = n + 1 + q) := hB'
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) ∨ a = n + 1 + q := hBa
    by_cases hx : (X : ℕ) ∈ g'.inputs
    · rcases hR p' g' hp' hx with e | e
      · rw [e]; exact key
      · exact absurd (Or.inr (by rw [e])) hB''
    · rcases hq with hq | hq
      · apply vl_congr gs M.hcl _ _ p' g' hp'
        intro a' ha'
        by_cases e1 : a' = n + 1 + q
        · rw [e1]; exact hq
        · exact hear a' ((M.hcl p' g' hp').lt a' ha')
            (fun hb => (hb : a' = (X : ℕ) ∨ a' = n + 1 + q).elim (fun e => hx (e ▸ ha')) e1)
      · rcases hBa' with e | e
        · exact absurd (e ▸ ha) hx
        · exact absurd (e ▸ ha) (hq p' g' hp')
  · exact fun (h : o = (X : ℕ) ∨ o = n + 1 + q) => h.elim
      (fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)) hqo

 

theorem Min.block2 (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z) (ho : ¬ B o)
    (u : Fin (n + 1) → Bool) (ha hb : ℕ) (ga gb : Gate) (hga : gs[ha]? = some ga)
    (hgb : gs[hb]? = some gb)
    (hout : ∀ p' g', gs[p']? = some g' → ¬ B (n + 1 + p') → (∃ a ∈ g'.inputs, B a) →
      p' = ha ∨ p' = hb)
    (hopa : ga.op = GateOp.and ∨ ga.op = GateOp.or) (w : ℕ) (hw : w ∈ ga.inputs) (hBw : ¬ B w)
    (hv : vl gs u w = fixBit ga)
    (hagree : ∀ a ∈ gb.inputs, B a → vl gs (Function.update u Z (!u Z)) a = vl gs u a) :
    False := by
  apply M.hdep Z u
  refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' _ hB' hr hear
    rcases hout p' g' hp' hB' hr with e | e
    · rw [e] at hear ⊢
      have hwlt : w < n + 1 + ha := (M.hcl ha ga hga).lt w hw
      rw [vl_abs gs M.hcl _ ha ga hga hopa w hw (by rw [hear w hwlt hBw]; exact hv),
        vl_abs gs M.hcl u ha ga hga hopa w hw hv]
    · rw [e] at hear ⊢
      apply vl_congr gs M.hcl _ _ hb gb hgb
      intro a haa
      by_cases hBa : B a
      · exact hagree a haa hBa
      · exact hear a ((M.hcl hb gb hgb).lt a haa) hBa

 

theorem Min.before (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z)
    (u : Fin (n + 1) → Bool) (w : ℕ) (hBw : ¬ B w)
    (hne : vl gs (Function.update u Z (!u Z)) w ≠ vl gs u w) :
    ∃ p' g', gs[p']? = some g' ∧ n + 1 + p' ≤ w ∧ ¬ B (n + 1 + p') ∧ ∃ a ∈ g'.inputs, B a := by
  by_contra hno
  apply hne
  refine agree_B gs M.hcl _ _ B (w + 1) ?_ ?_ w (by omega) hBw
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' hlt hB' hr _
    exact (hno ⟨p', g', hp', by omega, hB', hr⟩).elim

 
theorem Min.second (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs := by
  by_contra hno
  have hu : ∀ v : Fin (n + 1) → Bool, v Y = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun v hv => vl_abs gs M.hcl v pG gG hG hop Y hY (by rw [vl_input gs v Y Y.isLt]; exact hv)
  apply M.hdep X (fun _ => fixBit gG)
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ)) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ)) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (congrArg Fin.val e)) _ _
  · intro p g hp _ _ hr _
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) := hBa
    have hpG : p = pG := by
      by_contra hne
      exact hno ⟨p, g, hne, hp, hBa' ▸ ha⟩
    rw [hpG]
    rw [hu _ (by rw [Function.update_of_ne hXY.symm]), hu _ rfl]
  · exact fun (e : o = (X : ℕ)) => M.out X false false (by rw [e]; exact stF_self n gs X false)

 

theorem Min.side (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs ∧
      (∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) ∧
      IsC n gs X (!fixBit gG) (n + 1 + r) ∧ fixBit gr = !fixBit gG ∧
      (gr.op = GateOp.and ∨ gr.op = GateOp.or) ∧ (n + 1 + pG) ∉ gr.inputs := by
  have cG : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  obtain ⟨r, gr, hrG, hr, hXr⟩ := M.second X Y hXY pG gG hG hop hY
  have ncr : ¬ IsC n gs X (fixBit gG) (n + 1 + r) :=
    fun h => M.one_const X _ pG r (Ne.symm hrG) gG gr hG hr cG h
  have cr := M.reader_const X r gr hr hXr
  have hfr : fixBit gr = !fixBit gG := by
    by_contra hne
    apply ncr
    have e : fixBit gr = fixBit gG := by
      revert hne
      cases fixBit gr <;> cases fixBit gG <;> simp
    rw [← e]; exact cr
  have cr' : IsC n gs X (!fixBit gG) (n + 1 + r) := by rw [← hfr]; exact cr
  refine ⟨r, gr, hrG, hr, hXr, ?_, cr', hfr, ?_, ?_⟩
  · intro p' g' hp' hx
    by_contra hne
    have h1 : p' ≠ r := fun e => hne (Or.inl e)
    have h2 : p' ≠ pG := fun e => hne (Or.inr e)
    have cp := M.reader_const X p' g' hp' hx
    by_cases e : fixBit g' = fixBit gG
    · rw [e] at cp
      exact M.one_const X _ pG p' (Ne.symm h2) gG g' hG hp' cG cp
    · have e' : fixBit g' = !fixBit gG := by
        revert e
        cases fixBit g' <;> cases fixBit gG <;> simp
      rw [e'] at cp
      exact M.one_const X _ r p' (Ne.symm h1) gr g' hr hp' cr' cp
  · rcases M.hcl r gr hr with ⟨hopn, _⟩ | ⟨h, _⟩
    · exact (M.no_not X r gr hr hopn hXr).elim
    · exact h
  · intro hGr
    obtain ⟨c0, hc0⟩ := cG
    obtain ⟨_, _, w, hw, hwn⟩ := st_shape n gs M.hcl X (fixBit gG) r gr hr (n + 1 + pG) hGr c0 hc0
      (fun c' h => ncr ⟨c', h⟩)
    rcases two_inputs (M.hcl r gr hr) (X : ℕ) (n + 1 + pG) w hXr hGr
      (by have := X.isLt; omega) hw with e | e
    · exact hwn _ (by rw [e]; exact stF_self n gs X _)
    · exact hwn c0 (by rw [e]; exact hc0)

 
theorem Min.pair_false (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) : False := by
  have hXYn : (X : ℕ) ≠ (Y : ℕ) := fun e => hXY (Fin.ext e)
  obtain ⟨r, gr, hrG, hr, hXr, hRX, crX, hfr, hopr, hGr⟩ := M.side X Y hXY pG gG hG hop hX hY
  obtain ⟨r', gr', hr'G, hr', hYr', hRY, _, _, _, hGr'⟩ :=
    M.side Y X hXY.symm pG gG hG hop hY hX
  have cGX : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  have cGY : IsC n gs Y (fixBit gG) (n + 1 + pG) := M.reader_const Y pG gG hG hY
  have hoX : o ≠ (X : ℕ) := fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)
  have hoY : o ≠ (Y : ℕ) := fun e => M.out Y false false (by rw [e]; exact stF_self n gs Y false)
  have hoG : o ≠ n + 1 + pG := fun e => by
    have ⟨c, hc⟩ := cGX
    exact M.out X _ c (by rw [e]; exact hc)
  have hor : o ≠ n + 1 + r := fun e => by
    have ⟨c, hc⟩ := crX
    exact M.out X _ c (by rw [e]; exact hc)
  have hGv : ∀ (Z : Fin (n + 1)) (v : Fin (n + 1) → Bool), (Z : ℕ) ∈ gG.inputs →
      v Z = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun Z v hZ hv => vl_abs gs M.hcl v pG gG hG hop Z hZ (by rw [vl_input gs v Z Z.isLt]; exact hv)
  have hrX : ∀ v : Fin (n + 1) → Bool, v X = fixBit gr → vl gs v (n + 1 + r) = fixBit gr :=
    fun v hv => vl_abs gs M.hcl v r gr hr hopr X hXr (by rw [vl_input gs v X X.isLt]; exact hv)
  have hGin : ∀ w ∈ gG.inputs, w = (X : ℕ) ∨ w = (Y : ℕ) :=
    fun w hw => two_inputs (M.hcl pG gG hG) X Y w hX hY hXYn hw
  have fX : ∀ u : Fin (n + 1) → Bool, u Y = fixBit gG → vl gs u (n + 1 + r) = u X := fun u hu =>
    M.forced X r pG gr hr hXr hRX hoG u (Or.inl (by
      rw [hGv Y _ hY (by rw [Function.update_of_ne hXY.symm]; exact hu), hGv Y u hY hu]))
  have hex1 : ∃ (h1 : ℕ) (g1 : Gate), gs[h1]? = some g1 ∧ (n + 1 + pG) ∈ g1.inputs := by
    by_contra hno
    refine M.m2 r gr hr X (by have := X.isLt; omega) (fun u => ?_)
    rw [vl_input gs u X X.isLt]
    exact M.forced X r pG gr hr hXr hRX hoG u
      (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
  obtain ⟨h1, g1, hg1, hGh1⟩ := hex1
  have h1G : h1 ≠ pG := fun e => by
    have := (M.hcl h1 g1 hg1).lt _ hGh1
    omega
  have h1r : h1 ≠ r := fun e => hGr (gate_eq hg1 hr e ▸ hGh1)
  have h1r' : h1 ≠ r' := fun e => hGr' (gate_eq hg1 hr' e ▸ hGh1)
  by_cases hrr : r = r'
  swap
  · by_cases hrc : RC n gs Y (fixBit gG) r
    · exact M.nf4 Y (fixBit gG) pG r' h1 r (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm hrG)
        (Ne.symm h1r') (Ne.symm hrr) h1r ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩
        ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩ ⟨g1, hg1, _, hGh1, cGY⟩ hrc
    · obtain ⟨q, hnq, hq⟩ := st_fresh n gs M.hcl Y (fixBit gG) r gr hr
        (fun a ha c hc => hrc ⟨gr, hr, a, ha, c, hc⟩)
      obtain ⟨k, hk, hkX⟩ := st_other n gs Y (fixBit gG) X hXY
      refine M.ndup Y (fixBit gG) pG r' h1 (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm h1r')
        ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩ ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩
        ⟨g1, hg1, _, hGh1, cGY⟩ (n + 1 + r) X q k hq hnq hkX (by omega) (fun y => ?_)
      rw [vl_input gs _ X X.isLt]
      exact fX _ (by simp [ins])
  · have hRY' : ∀ p' g', gs[p']? = some g' → (Y : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG := by
      intro p' g' hp' hy
      rw [hrr]; exact hRY p' g' hp' hy
    have hex2 : ∃ (h2 : ℕ) (g2 : Gate), gs[h2]? = some g2 ∧ (n + 1 + r) ∈ g2.inputs := by
      by_contra hno
      refine M.m2 pG gG hG X (by have := X.isLt; omega) (fun u => ?_)
      rw [vl_input gs u X X.isLt]
      exact M.forced X pG r gG hG hX (fun p' g' hp' hx => (hRX p' g' hp' hx).symm) hor u
        (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
    obtain ⟨h2, g2, hg2, hrh2⟩ := hex2
    have hrG' : (n + 1 + r) ∉ gG.inputs := fun h => by
      rcases hGin _ h with e | e
      · have := X.isLt; omega
      · have := Y.isLt; omega
    have h2r : h2 ≠ r := fun e => by
      have := (M.hcl h2 g2 hg2).lt _ hrh2
      omega
    have h2G : h2 ≠ pG := fun e => hrG' (gate_eq hg2 hG e ▸ hrh2)
    have h1u : ∀ p' g', gs[p']? = some g' → (n + 1 + pG) ∈ g'.inputs → p' = h1 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      have e2 : p' ≠ r := fun e => hGr (gate_eq hp' hr e ▸ hin)
      exact M.nf4 X (fixBit gG) pG r h1 p' (Ne.symm hrG) (Ne.symm h1G) (Ne.symm e1)
        (Ne.symm h1r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g1, hg1, _, hGh1, cGX⟩ ⟨g', hp', _, hin, cGX⟩
    have h2u : ∀ p' g', gs[p']? = some g' → (n + 1 + r) ∈ g'.inputs → p' = h2 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => hrG' (gate_eq hp' hG e ▸ hin)
      have e2 : p' ≠ r := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      exact M.nf4 X (!fixBit gG) pG r h2 p' (Ne.symm hrG) (Ne.symm h2G) (Ne.symm e1)
        (Ne.symm h2r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g2, hg2, _, hrh2, crX⟩ ⟨g', hp', _, hin, crX⟩
    have n1X : ¬ IsC n gs X (fixBit gG) (n + 1 + h1) :=
      fun h => M.one_const X _ pG h1 (Ne.symm h1G) gG g1 hG hg1 cGX h
    have n2X : ¬ IsC n gs X (!fixBit gG) (n + 1 + h2) :=
      fun h => M.one_const X _ r h2 (Ne.symm h2r) gr g2 hr hg2 crX h
    have ⟨cg, hcg⟩ := cGX
    have ⟨cr, hcr⟩ := crX
    obtain ⟨hop1, hf1, w1, hw1, hw1n⟩ := st_shape n gs M.hcl X (fixBit gG) h1 g1 hg1 _ hGh1 cg hcg
      (fun c' h => n1X ⟨c', h⟩)
    obtain ⟨hop2, hf2, w2, hw2, hw2n⟩ := st_shape n gs M.hcl X (!fixBit gG) h2 g2 hg2 _ hrh2 cr
      hcr (fun c' h => n2X ⟨c', h⟩)
    have hcgv : cg = fixBit gG := by
      have h := st_val_const n gs M.hcl X (fixBit gG) (n + 1 + pG) cg hcg (fun _ => false)
      rw [hGv X _ hX (by simp [ins])] at h
      exact h.symm
    have hcrv : cr = fixBit gr := by
      have h := st_val_const n gs M.hcl X (!fixBit gG) (n + 1 + r) cr hcr (fun _ => false)
      rw [hrX _ (by simp [ins, hfr])] at h
      exact h.symm
    have f1 : fixBit g1 = !fixBit gG := by
      rw [hcgv] at hf1
      revert hf1
      cases fixBit g1 <;> cases fixBit gG <;> simp
    have f2 : fixBit g2 = fixBit gG := by
      rw [hcrv, hfr] at hf2
      revert hf2
      cases fixBit g2 <;> cases fixBit gG <;> simp
    have h12 : h1 ≠ h2 := fun e => by
      have e' : g1 = g2 := gate_eq hg1 hg2 e
      rw [e', f2] at f1
      revert f1
      cases fixBit gG <;> simp
    have hr1 : (n + 1 + r) ∉ g1.inputs := fun h => h12 (h2u h1 g1 hg1 h)
    have hG2 : (n + 1 + pG) ∉ g2.inputs := fun h => h12 (h1u h2 g2 hg2 h).symm
    have hX1 : (X : ℕ) ∉ g1.inputs := fun h => (hRX h1 g1 hg1 h).elim h1r h1G
    have hY1 : (Y : ℕ) ∉ g1.inputs := fun h => (hRY' h1 g1 hg1 h).elim h1r h1G
    have hX2 : (X : ℕ) ∉ g2.inputs := fun h => (hRX h2 g2 hg2 h).elim h2r h2G
    have hY2 : (Y : ℕ) ∉ g2.inputs := fun h => (hRY' h2 g2 hg2 h).elim h2r h2G
    have hBw1X : ¬ (w1 = (X : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw1Y : ¬ (w1 = (Y : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw2X : ¬ (w2 = (X : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hBw2Y : ¬ (w2 = (Y : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hout : ∀ (Z : Fin (n + 1)),
        (∀ p' g', gs[p']? = some g' → (Z : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) →
        ∀ p' g', gs[p']? = some g' →
          ¬ (n + 1 + p' = (Z : ℕ) ∨ n + 1 + p' = n + 1 + pG ∨ n + 1 + p' = n + 1 + r) →
          (∃ a ∈ g'.inputs, a = (Z : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) →
          p' = h1 ∨ p' = h2 := by
      intro Z hRZ p' g' hp' hB hr
      obtain ⟨a, ha, hBa⟩ := hr
      rcases hBa with e | e | e
      · exfalso
        rcases hRZ p' g' hp' (e ▸ ha) with e' | e'
        · exact hB (Or.inr (Or.inr (by rw [e'])))
        · exact hB (Or.inr (Or.inl (by rw [e'])))
      · exact Or.inl (h1u p' g' hp' (e ▸ ha))
      · exact Or.inr (h2u p' g' hp' (e ▸ ha))
    have hoBY : ¬ (o = (Y : ℕ) ∨ o = n + 1 + pG ∨ o = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hoY e
      · exact hoG e
      · exact hor e
    have A2 : ∀ u : Fin (n + 1) → Bool, vl gs u w2 = fixBit gG → u X = fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h2 h1 g2 g1 hg2 hg1 (fun p' g' hp' hB hr => (hout Y hRY' p' g' hp' hB hr).symm)
        hop2 w2 hw2 hBw2Y (by rw [f2]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY1
      · rw [e, hGv X _ hX (by rw [Function.update_of_ne hXY]; exact hx), hGv X u hX hx]
      · exact absurd (e ▸ ha) hr1
    have A4 : ∀ u : Fin (n + 1) → Bool, vl gs u w1 = !fixBit gG → u X = !fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h1 h2 g1 g2 hg1 hg2 (hout Y hRY') hop1 w1 hw1 hBw1Y (by rw [f1]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY2
      · exact absurd (e ▸ ha) hG2
      · rw [e, hrX _ (by rw [Function.update_of_ne hXY, hfr]; exact hx),
          hrX u (by rw [hfr]; exact hx)]
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    have hl2 : h2 < gs.length := (List.getElem?_eq_some_iff.1 hg2).1
    have hw1lt := (M.hcl h1 g1 hg1).lt w1 hw1
    have hw2lt := (M.hcl h2 g2 hg2).lt w2 hw2
    have lt12 : h1 < h2 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w2 (by omega) (fixBit gG)
      have hx : u X = !fixBit gG := by
        have h := A2 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w2 ≠ vl gs u w2 := fun e =>
        A2 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w2 hBw2X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    have lt21 : h2 < h1 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w1 (by omega) (!fixBit gG)
      have hx : u X = fixBit gG := by
        have h := A4 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w1 ≠ vl gs u w1 := fun e =>
        A4 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w1 hBw1X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    omega

 
theorem Min.contra (M : Min n gs o) : False := by
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases hgs : gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := M.reader 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        (fun (e : o = ((0 : Fin (n + 1)) : ℕ)) =>
          M.out 0 false false (by rw [e]; exact stF_self n gs 0 false))
      rw [hgs] at hp
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases M.hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact M.no_not ⟨j, by omega⟩ 0 g0 h0 hop (by rw [hin]; simp)
  · by_cases hjk : j = k
    · refine M.m2 0 g0 h0 j (by omega) (fun u => ?_)
      rw [vl_gate gs M.hcl u 0 g0 h0, hin, hjk]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
    · exact M.pair_false ⟨j, by omega⟩ ⟨k, by omega⟩ (fun e => hjk (congrArg Fin.val e)) 0 g0 h0
        hop (by rw [hin]; simp) (by rw [hin]; simp)

end

 

 
theorem par_lower4 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 4 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    classical
    have hex : ∃ t, HasClean (n + 1 + 1)
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) t := ⟨s, h⟩
    obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
    have hfs : Nat.find hex ≤ s := Nat.find_min' hex h
    have hev' : ∀ x : Fin (n + 1 + 1) → Bool, vl gs x o = xor (par (n + 1 + 1) x) c := hev
    have hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL (n + 1 + 1) gs' →
        (∀ x : Fin (n + 1 + 1) → Bool, vl gs' x o' = xor (par (n + 1 + 1) x) c) →
        gs.length ≤ gs'.length := by
      intro gs' o' hc' he'
      by_contra hlt
      exact Nat.find_min hex (m := gs'.length) (by omega) ⟨gs', o', hc', le_refl _, he'⟩
    suffices 4 * (n + 1) ≤ gs.length by omega
    by_contra hsmall
    have hncf : ∃ y y' : Fin (n + 1 + 1) → Bool, vl gs y o ≠ vl gs y' o := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      rw [hev', hev', par_snoc, par_snoc]
      cases par (n + 1) (fun _ => false) <;> cases c <;> simp
    have M : Min (n + 1) gs o :=
      { hcl := hcl
        hdep := by
          intro i u
          rw [hev', hev', par_flip]
          cases par (n + 1 + 1) u <;> cases c <;> simp
        hnc := by
          intro i b
          refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
          rw [hev', hev', par_insertNth, par_insertNth, par_snoc, par_snoc]
          cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
        m1 := by
          intro p g hp c' hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ := drop_const (n + 1 + 1) gs hcl o p c' hpl hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        m2 := by
          intro p g hp j hj hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ :=
            drop_alias (n + 1 + 1) gs hcl o p j hpl hj hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        nored := by
          rintro ⟨i, b, gs', o', hc', hl', he'⟩
          have h' : HasClean (n + 1)
              (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c)) gs'.length :=
            ⟨gs', o', hc', le_refl _, fun y => by
              show vl gs' y o' = _
              rw [he' y, hev', par_insertNth, Bool.xor_assoc]⟩
          have := ih _ _ h'
          omega }
    exact M.contra

 
theorem parity_lower4 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    4 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower4 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.Outside.L_meta_191_PathLib

-- Adapted from PEqualNP.MetaComplexity.Helpers.PermInputs in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

 

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

 
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

 
theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

 
theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

 

theorem fix_many {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) :
    ∀ (L : List (Fin N)) (f : (Fin N → Bool) → Bool), L.Nodup → (∀ p ∈ L, p ∉ T) →
    (∀ (a : Fin N → Bool) (pre post : List (Fin N)) (p : Fin N), L = pre ++ p :: post →
      ∃ x : Fin N → Bool, (∀ q ∈ pre, x q = a q) ∧ f (Function.update x p (!x p)) ≠ f x) →
    (∀ (a : Fin N → Bool), ∀ i ∈ T, ∃ x : Fin N → Bool, (∀ q ∈ L, x q = a q) ∧
      f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, HasCircuitSize N f s → T.card + 2 * L.length ≤ s + 1 := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i0.2; omega⟩
  intro L
  induction L with
  | nil =>
    intro f _ _ _ hC s h
    have := dep_lower_set (n + 1) f T (fun i hi => by
      obtain ⟨x, _, hx⟩ := hC (fun _ => false) i hi
      exact ⟨x, hx⟩) s h
    simpa using this
  | cons p L ih =>
    intro f hnd hdis hA hC s h
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    have hpT : p ∉ T := hdis p List.mem_cons_self
    have hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x := by
      obtain ⟨x, _, hx⟩ := hA (fun _ => false) [] L p rfl
      exact ⟨x, hx⟩
    have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b) := by
      intro b
      obtain ⟨x, hxa, hx⟩ := hC (fun _ => b) i0 hi0
      have hxp : x p = b := hxa p List.mem_cons_self
      have hi0p : i0 ≠ p := fun e => hpT (e ▸ hi0)
      refine ⟨Function.update x i0 (!x i0), x, ?_⟩
      have e1 : Function.update (Function.update x i0 (!x i0)) p b
          = Function.update x i0 (!x i0) :=
        Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hi0p), hxp])
      have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
      rw [e1, e2]
      exact hx
    obtain ⟨b, s', hs, h'⟩ := gate_elim_at n f p s hdep hnc h
    have := ih (fun x => f (Function.update x p b)) (List.nodup_cons.1 hnd).2
      (fun q hq => hdis q (List.mem_cons_of_mem _ hq)) ?_ ?_ s' h'
    · simp only [List.length_cons]; omega
    · intro a pre post p' hL
      obtain ⟨x, hxa, hx⟩ := hA (Function.update a p b) (p :: pre) post p' (by rw [hL]; rfl)
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hp' : p' ≠ p := by
        intro e; apply hpL; rw [← e, hL]; simp
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro e; apply hpL; rw [← e, hL]; simp [hq]
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x p' (!x p')) p b
            = Function.update x p' (!x p') :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hp'), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
    · intro a i hi
      obtain ⟨x, hxa, hx⟩ := hC (Function.update a p b) i hi
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hip : i ≠ p := fun e => hpT (e ▸ hi)
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := fun e => hpL (e ▸ hq)
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x i (!x i)) p b
            = Function.update x i (!x i) :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hip), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx

end PEqualNP.Outside.L_meta_191_PathLib.PermInputs

-- Adapted from PEqualNP.MetaComplexity.Helpers.ForestElim in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_191_PathLib.PermInputs

 
theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.Outside.L_meta_191_PathLib.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.Outside.L_meta_191_PathLib.Forest

-- Adapted from PEqualNP.MetaComplexity.Helpers.Readers in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_191_PathLib
open PEqualNP.Outside.L_meta_191_PathLib.PermInputs

 

 
def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

 
abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

 

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

 
def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

 
def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

 
def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

 
def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

 

 
structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

 
def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

 

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

 
theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

 

 
theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

 

 
theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

 

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

 
theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

 
theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

 
theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

 
theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

 
theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end

 

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

 

theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

 

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  PEqualNP.Outside.L_meta_191_PathLib.Readers.save n f gs o L.hcl L.hev i b hnc S hS

theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

 
theorem Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega

 

theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end

end PEqualNP.Outside.L_meta_191_PathLib.Readers

-- Adapted from PEqualNP.MetaComplexity.Helpers.ReadersPat in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_191_PathLib

 
theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

 
theorem Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)

end

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

 

theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

 
theorem Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc

 
theorem Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc

 
theorem Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩

 
theorem Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩

end

end PEqualNP.Outside.L_meta_191_PathLib.Readers

-- Adapted from PEqualNP.MetaComplexity.Helpers.ReadersFunnel in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_191_PathLib

 
theorem lit_contra {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool)
    (h : ∀ u, f u = xor (u v) c) : False := by
  have hd : Dep f v := ⟨fun _ => false, by rw [h, h]; cases c <;> simp⟩
  obtain ⟨x, y, hxy⟩ := hnc v hd false
  apply hxy
  rw [h, h]
  simp

theorem set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]

theorem set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]

theorem set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

 
theorem Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (r : ℕ) (hr : r < t)
    (g : Gate) (hg : gs[r]? = some g) : ∃ v : Fin (n + 1), g.inputs = [(v : ℕ)] := by
  rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
  · by_cases hjn : j < n + 1
    · exact ⟨⟨j, hjn⟩, hin⟩
    · exfalso
      obtain ⟨r', rfl⟩ : ∃ r', j = n + 1 + r' := ⟨j - (n + 1), by omega⟩
      have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      obtain ⟨g', hg'⟩ : ∃ g', gs[r']? = some g' :=
        ⟨gs[r'], List.getElem?_eq_getElem (by omega)⟩
      have hop' := ht r' (by omega) g' hg'
      rcases L.hcl r' g' hg' with ⟨_, j', hj', hin'⟩ | ⟨hop2, _⟩
      · exact L.no_alias hfnc r hrl j' (by omega) (fun u => by
          rw [vl_not gs L.hcl u r g hg _ hop hin, vl_not gs L.hcl u r' g' hg' _ hop' hin']
          simp)
      · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
  · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h

 
theorem Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (w : ℕ)
    (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) :
    ∃ (v : Fin (n + 1)) (c : Bool), (∀ u, vl gs u w = xor (u v) c) ∧
      (w = v ∨ ∃ r g, r < t ∧ w = n + 1 + r ∧ gs[r]? = some g ∧ g.op = GateOp.not ∧
        g.inputs = [(v : ℕ)]) := by
  by_cases hwn : w < n + 1
  · exact ⟨⟨w, hwn⟩, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, gs[r]? = some g := ⟨gs[r], List.getElem?_eq_getElem (by omega)⟩
    have hop := ht r (by omega) g hg
    obtain ⟨v, hin⟩ := L.not_input hfnc t ht r (by omega) g hg
    exact ⟨v, true, fun u => by
      rw [vl_not gs L.hcl u r g hg _ hop hin, vl_input gs u v v.isLt]; simp,
      Or.inr ⟨r, g, by omega, rfl, hg, hop, hin⟩⟩

 

theorem Least.funnel (L : Least (n + 1) f gs o) (hdep : ∃ p, Dep f p) (hnc : RestrNC f)
    (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ), Reads gs p i → Reads gs q i → p = q)
    (h2 : ∀ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g → g.op = GateOp.not →
      (i : ℕ) ∈ g.inputs → ∀ p q : ℕ, Reads gs p (n + 1 + r) → Reads gs q (n + 1 + r) → p = q) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  by_cases hex : ∃ (t : ℕ) (g : Gate), gs[t]? = some g ∧ g.op ≠ GateOp.not
  swap
  · exfalso
    push Not at hex
    have ht : ∀ r < gs.length, ∀ g, gs[r]? = some g → g.op = GateOp.not :=
      fun r _ g hg => hex r g hg
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨v, c, hv, _⟩ := L.lit_wire hfnc gs.length ht o hol hol
      exact lit_contra hnc v c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, y, hxy⟩ := hfnc
      apply hxy
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]
  obtain ⟨g, hg, hgop⟩ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht : ∀ r < t, ∀ g', gs[r]? = some g' → g'.op = GateOp.not := by
    intro r hr g' hg'
    by_contra hne
    exact Nat.find_min hex hr ⟨g', hg', hne⟩
  have htl : t < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rcases L.hcl t g hg with ⟨hop, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hop hgop
  obtain ⟨vj, cj, hvj, hsj⟩ := L.lit_wire hfnc t ht j hj (by omega)
  obtain ⟨vk, ck, hvk, hsk⟩ := L.lit_wire hfnc t ht k hk (by omega)
  have hRj : Reads gs t j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs t k := ⟨g, hg, by rw [hin]; simp⟩
  
  have hRv : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) → ∃ r, Reads gs r v := by
    intro w v hw hs
    rcases hs with e | ⟨r, g', _, _, hg', _, hin'⟩
    · exact ⟨t, by rw [← e]; exact hw⟩
    · exact ⟨r, g', hg', by rw [hin']; simp⟩
  
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = t := by
    intro w v hw hs p' a ha hr hne
    rcases hs with e | ⟨r, g', _, er, hg', hop', hin'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact h1 v p' t hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨g', hg', by rw [hin']; simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := h1 v p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact h2 v r g' hg' hop' (by rw [hin']; simp) p' t hr hw
  
  have hvjk : vj ≠ vk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc t htl j hj (fun u => by
        rw [vl_gate gs L.hcl u t g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, g1, hr1, ej, hg1, hop1, hin1⟩ <;>
      rcases hsk with ek | ⟨r2, g2, hr2, ek, hg2, hop2, hin2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := h1 vj t r2 (by rw [← ej]; exact hRj) ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      omega
    · have := h1 vk t r1 (by rw [← ek]; exact hRk) ⟨g1, hg1, by rw [hin1, e]; simp⟩
      omega
    · have := h1 vj r1 r2 ⟨g1, hg1, by rw [hin1]; simp⟩ ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  obtain ⟨rj, hrj⟩ := hRv j vj hRj hsj
  obtain ⟨rk, hrk⟩ := hRv k vk hRk hsk
  have hdj := L.read_dep hfnc vj rj hrj
  have hdk := L.read_dep hfnc vk rk hrk
  
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ vj → i ≠ vk → u i = u' i) →
      vl gs u (n + 1 + t) = vl gs u' (n + 1 + t) → f u = f u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (vj : ℕ) ∨ n + 1 + p' = (vk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = t := by
        rcases hBa' with e | e | e | e
        · exact hopnd j vj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j vj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (vj : ℕ) ∨ o = (vk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact lit_contra hnc vj false (fun x => by
          rw [← L.hev, e, vl_input gs x vj vj.isLt]; simp)
      · exact lit_contra hnc vk false (fun x => by
          rw [← L.hev, e, vl_input gs x vk vk.isLt]; simp)
      · exact lit_contra hnc vj cj (fun x => by rw [← L.hev, e, hvj])
      · exact lit_contra hnc vk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ vj → i ≠ vk →
      set2 x vj a vk b i = set2 x vj a' vk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x vj vk a b i e1 e2, set2_o x vj vk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x vj a vk b) (n + 1 + t) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ t g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  refine ⟨vj, vk, hvjk, hdj, hdk, ?_⟩
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

end

end PEqualNP.Outside.L_meta_191_PathLib.Readers

-- Adapted from PEqualNP.MetaComplexity.Helpers.ReadersExport in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_191_PathLib

 

theorem fanout_step (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    ∃ y : Fin (n + 1), Dep f y ∧ Pays f y s := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc h
  have mono : ∀ y, Pays f y gs.length → Pays f y s := by
    intro y hp
    rcases hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩
    · exact Or.inr (Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
    · exact Or.inr (Or.inr ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
  by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ), p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, p, q, hpq, hp, hq⟩ := hA
    have hd := L.read_dep hfnc i p hp
    exact ⟨i, hd, mono i (L.two_readers i (hnc i hd) p q hpq hp hq)⟩
  by_cases hB : ∃ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g ∧ g.op = GateOp.not ∧
      (i : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ, p ≠ q ∧ Reads gs p (n + 1 + r) ∧ Reads gs q (n + 1 + r)
  · obtain ⟨i, r, g, hr, hop, hin, p, q, hpq, hp, hq⟩ := hB
    have hd := L.read_dep hfnc i r ⟨g, hr, hin⟩
    obtain ⟨d1, d2⟩ := L.not_two_readers i (hnc i hd) r g hr hop hin p q hpq hp hq
    exact ⟨i, hd, mono i (Or.inl ⟨d1, d2⟩)⟩
  exfalso
  obtain ⟨p, q, hpq, hdp, hdq, hf⟩ := L.funnel hdep hnc
    (fun i p q hp hq => by
      by_contra hne
      exact hA ⟨i, p, q, hne, hp, hq⟩)
    (fun i r g hr hop hin p q hp hq => by
      by_contra hne
      exact hB ⟨i, r, g, hr, hop, hin, p, q, hne, hp, hq⟩)
  exact hnf p q hpq hdp hdq hf

 
theorem fanout_step_3_4 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨
      (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') := by
  obtain ⟨y, _, hp⟩ := fanout_step n f s hdep hnc hnf h
  rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
  · exact Or.inl ⟨y, s', h1, h2⟩
  · exact Or.inl ⟨y, s', by omega, h2⟩
  · exact Or.inr ⟨y, s', h1, h2⟩

 

theorem noFunnel_of_sep {m : ℕ} (f : (Fin m → Bool) → Bool)
    (h : ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q →
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p false q true) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q true))) : NoFunnel f := by
  intro p q hpq hdp hdq hf
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩⟩ := h p q hpq hdp hdq
  cases a <;> cases b
  · exact h3 (hab x3).1
  · exact h1 (hab x1).2.symm
  · exact h2 ((hab x2).1.trans (hab x2).2).symm
  · exact h1 (hab x1).2

end PEqualNP.Outside.L_meta_191_PathLib.Readers

-- Adapted from PEqualNP.MetaComplexity.L107 in the Apache-2.0 project.
theorem PEqualNP.Outside.L_meta_191_PathLib.readerTheorem : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ), (∃ p : Fin (n + 1), ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∀ p : Fin (n + 1), (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) → (∀ p q : Fin (n + 1), p ≠ q → (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∃ x : Fin (n + 1) → Bool, f (Function.update x q (!x q)) ≠ f x) → ¬ ∃ a b : Bool, ∀ x : Fin (n + 1) → Bool, f (Function.update (Function.update x p (!a)) q b) = f (Function.update (Function.update x p a) q (!b)) ∧ f (Function.update (Function.update x p a) q (!b)) = f (Function.update (Function.update x p (!a)) q (!b))) → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s → (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨ (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') :=
  PEqualNP.Outside.L_meta_191_PathLib.Readers.fanout_step_3_4

-- Adapted from PEqualNP.MetaComplexity.Helpers.PathSizeLower in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_191_PathLib.PathSize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_191_PathLib
open PEqualNP.Outside.L_meta_191_PathLib.PermInputs

 
def G (N k : ℕ) (x : Fin N → Bool) : Bool :=
  decide ((∃ i : Fin N, i.val < k ∧ x i = true) ∨
    (∃ i j : Fin N, k ≤ i.val ∧ i.val + 1 = j.val ∧ x i = true ∧ x j = true))

 
def ext {N : ℕ} (x : Fin N → Bool) (j : ℕ) : Bool := if h : j < N then x ⟨j, h⟩ else false

theorem ext_fin {N : ℕ} (x : Fin N → Bool) (i : Fin N) : ext x i.val = x i := by
  simp [ext]

theorem ext_lt {N : ℕ} {x : Fin N → Bool} {j : ℕ} (h : ext x j = true) : j < N := by
  unfold ext at h
  split at h
  · assumption
  · simp at h

theorem ext_ge {N : ℕ} (x : Fin N → Bool) {j : ℕ} (h : N ≤ j) : ext x j = false := by
  unfold ext
  rw [dif_neg (by omega)]

theorem ext_fn {N : ℕ} (Q : ℕ → Bool) (j : ℕ) :
    ext (fun i : Fin N => Q i.val) j = (decide (j < N) && Q j) := by
  unfold ext
  by_cases hj : j < N <;> simp [hj]

theorem ext_update {N : ℕ} (x : Fin N → Bool) (p : Fin N) (b : Bool) (j : ℕ) :
    ext (Function.update x p b) j = if j = p.val then b else ext x j := by
  unfold ext
  by_cases hj : j < N
  · simp [hj, Function.update_apply, Fin.ext_iff]
  · have : j ≠ p.val := by have := p.2; omega
    simp [hj, this]

theorem G_iff (N k : ℕ) (x : Fin N → Bool) : G N k x = true ↔
    ((∃ i, i < k ∧ ext x i = true) ∨ (∃ i, k ≤ i ∧ ext x i = true ∧ ext x (i + 1) = true)) := by
  unfold G
  rw [decide_eq_true_iff]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, j, hi, hij, hx, hy⟩)
    · exact Or.inl ⟨i, hi, by rw [ext_fin]; exact hx⟩
    · refine Or.inr ⟨i, hi, by rw [ext_fin]; exact hx, ?_⟩
      rw [hij, ext_fin]; exact hy
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · have hl := ext_lt hx
      refine Or.inl ⟨⟨i, hl⟩, hi, ?_⟩
      rw [← ext_fin x ⟨i, hl⟩]; exact hx
    · have hl := ext_lt hy
      refine Or.inr ⟨⟨i, by omega⟩, ⟨i + 1, hl⟩, hi, rfl, ?_, ?_⟩
      · rw [← ext_fin x ⟨i, by omega⟩]; exact hx
      · rw [← ext_fin x ⟨i + 1, hl⟩]; exact hy

 
def del (n k : ℕ) (hk : k < n) : Fin (n + 1) → Fin n :=
  fun i => ⟨if i.val ≤ k then i.val else i.val - 1, by have := i.2; split <;> omega⟩

theorem ext_del (n k : ℕ) (hk : k < n) (y : Fin n → Bool) (b : Bool) (j : ℕ) :
    ext (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ b) j
      = if j = k then b else if j < k then ext y j else ext y (j - 1) := by
  rw [ext_update]
  by_cases hjk : j = k
  · simp [hjk]
  · rw [if_neg hjk, if_neg hjk]
    unfold ext
    by_cases hj : j < n + 1
    · rw [dif_pos hj]
      by_cases hjk' : j < k
      · rw [if_pos hjk', dif_pos (by omega)]
        simp [del, show j ≤ k by omega]
      · rw [if_neg hjk', dif_pos (by omega)]
        simp [del, show ¬ j ≤ k by omega]
    · rw [dif_neg hj, if_neg (by omega), dif_neg (by omega)]

theorem G_del_false (n k : ℕ) (hk : k < n) (y : Fin n → Bool) :
    G (n + 1) k (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ false) = G n k y := by
  rw [Bool.eq_iff_iff, G_iff, G_iff]
  simp only [ext_del]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · rw [if_neg (by omega), if_pos hi] at hx
      exact Or.inl ⟨i, hi, hx⟩
    · by_cases hik : i = k
      · rw [if_pos hik] at hx; exact absurd hx (by simp)
      · rw [if_neg hik, if_neg (by omega)] at hx
        rw [if_neg (by omega), if_neg (by omega)] at hy
        refine Or.inr ⟨i - 1, by omega, hx, ?_⟩
        rwa [show i - 1 + 1 = i + 1 - 1 by omega]
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · refine Or.inl ⟨i, hi, ?_⟩
      rw [if_neg (by omega), if_pos hi]; exact hx
    · refine Or.inr ⟨i + 1, by omega, ?_, ?_⟩
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hx
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hy

theorem G_del_true (n k : ℕ) (hk : k < n) (y : Fin n → Bool) :
    G (n + 1) k (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ true) = G n (k + 1) y := by
  rw [Bool.eq_iff_iff, G_iff, G_iff]
  simp only [ext_del]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · rw [if_neg (by omega), if_pos hi] at hx
      exact Or.inl ⟨i, by omega, hx⟩
    · by_cases hik : i = k
      · rw [if_neg (by omega), if_neg (by omega)] at hy
        refine Or.inl ⟨k, by omega, ?_⟩
        rwa [show k = i + 1 - 1 by omega]
      · by_cases hik1 : i = k + 1
        · rw [if_neg (by omega), if_neg (by omega)] at hx
          refine Or.inl ⟨k, by omega, ?_⟩
          rwa [show k = i - 1 by omega]
        · rw [if_neg hik, if_neg (by omega)] at hx
          rw [if_neg (by omega), if_neg (by omega)] at hy
          refine Or.inr ⟨i - 1, by omega, hx, ?_⟩
          rwa [show i - 1 + 1 = i + 1 - 1 by omega]
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · by_cases hik : i < k
      · refine Or.inl ⟨i, hik, ?_⟩
        rw [if_neg (by omega), if_pos hik]; exact hx
      · have e : i = k := by omega
        subst e
        refine Or.inr ⟨i, le_rfl, by simp, ?_⟩
        rw [if_neg (by omega), if_neg (by omega)]; simpa using hx
    · refine Or.inr ⟨i + 1, by omega, ?_, ?_⟩
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hx
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hy

 
theorem G_dep (N k : ℕ) (hd : k + 2 ≤ N) (p : Fin N) :
    ∃ x : Fin N → Bool, G N k (Function.update x p (!x p)) ≠ G N k x := by
  by_cases hp : p.val < k
  · refine ⟨fun _ => false, ?_⟩
    have h1 : G N k (Function.update (fun _ => false) p (!false)) = true := by
      rw [G_iff]
      refine Or.inl ⟨p.val, hp, ?_⟩
      rw [ext_update]; simp
    have h0 : G N k (fun _ => false) = false := by
      rw [← Bool.not_eq_true, G_iff]
      rintro (⟨i, _, hx⟩ | ⟨i, _, hx, _⟩) <;> simp [ext] at hx
    rw [h1, h0]; simp
  · set q : ℕ := if p.val + 1 < N then p.val + 1 else p.val - 1 with hq
    have hqN : q < N := by rw [hq]; split <;> omega
    have hqk : k ≤ q := by have := p.2; rw [hq]; split <;> omega
    have hpq : p.val ≠ q := by rw [hq]; split <;> omega
    refine ⟨fun i : Fin N => decide (i.val = q), ?_⟩
    have hxp : (fun i : Fin N => decide (i.val = q)) p = false := by simp [hpq]
    rw [hxp]
    have h1 : G N k (Function.update (fun i : Fin N => decide (i.val = q)) p (!false)) = true := by
      rw [G_iff]
      right
      by_cases hc : p.val + 1 < N
      · have hqv : q = p.val + 1 := by rw [hq, if_pos hc]
        refine ⟨p.val, by omega, ?_, ?_⟩
        · rw [ext_update]; simp
        · rw [ext_update, if_neg (by omega), ext_fn (fun j => decide (j = q))]; simp [hqv, hc]
      · have hqv : q = p.val - 1 := by rw [hq, if_neg hc]
        refine ⟨q, hqk, ?_, ?_⟩
        · rw [ext_update, if_neg (by omega), ext_fn (fun j => decide (j = q))]; simp [hqN]
        · rw [ext_update, if_pos (by omega)]; rfl
    have h0 : G N k (fun i : Fin N => decide (i.val = q)) = false := by
      rw [← Bool.not_eq_true, G_iff]
      rintro (⟨i, hi, hx⟩ | ⟨i, _, hx, hy⟩)
      · rw [ext_fn (fun j => decide (j = q))] at hx
        simp at hx; omega
      · rw [ext_fn (fun j => decide (j = q))] at hx hy
        simp at hx hy; omega
    rw [h1, h0]; simp

theorem hasCircuitSize_mono' {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t)
    (h : HasCircuitSize n f s) : HasCircuitSize n f t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hst, h3⟩

 
theorem G_lower : ∀ d : ℕ, 2 ≤ d → ∀ k N s : ℕ, N = k + d →
    HasCircuitSize N (G N k) s → N + d / 2 ≤ s + 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd k N s hN h
    by_cases hd4 : d < 4
    · have := dep_lower N (G N k) (G_dep N k (by omega)) s h
      have : d / 2 ≤ 1 := by omega
      omega
    · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      have hk : k < n := by omega
      set p : Fin (n + 1) := ⟨k, by omega⟩ with hp
      have hdep := G_dep (n + 1) k (by omega) p
      have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
          G (n + 1) k (Function.update x p b) ≠ G (n + 1) k (Function.update y p b) := by
        intro b
        refine ⟨fun _ => false, fun i : Fin (n + 1) => decide (i.val = k + 2 ∨ i.val = k + 3), ?_⟩
        have h0 : G (n + 1) k (Function.update (fun _ => false) p b) = false := by
          rw [← Bool.not_eq_true, G_iff]
          rintro (⟨i, hi, hx⟩ | ⟨i, _, hx, hy⟩)
          · rw [ext_update, if_neg (by simp [hp]; omega)] at hx
            simp [ext] at hx
          · rw [ext_update] at hx hy
            rw [if_neg (by simp [hp]; omega)] at hy
            simp [ext] at hy
        have h1 : G (n + 1) k (Function.update
            (fun i : Fin (n + 1) => decide (i.val = k + 2 ∨ i.val = k + 3)) p b) = true := by
          rw [G_iff]
          refine Or.inr ⟨k + 2, by omega, ?_, ?_⟩
          · rw [ext_update, if_neg (by simp [hp]),
              ext_fn (fun j => decide (j = k + 2 ∨ j = k + 3))]
            simp; omega
          · rw [ext_update, if_neg (by simp [hp]; omega),
              ext_fn (fun j => decide (j = k + 2 ∨ j = k + 3))]
            simp; omega
        rw [h0, h1]; simp
      obtain ⟨b, s', hs, h'⟩ := gate_elim_at n (G (n + 1) k) p s hdep hnc h
      have h'' := relabel_size (del n k hk) _ s' h'
      cases b with
      | false =>
        have e : (fun y : Fin n → Bool =>
            (fun x => G (n + 1) k (Function.update x p false)) (y ∘ del n k hk)) = G n k := by
          funext y; exact G_del_false n k hk y
        rw [e] at h''
        have := ih (d - 1) (by omega) (by omega) k n s' (by omega) h''
        omega
      | true =>
        have e : (fun y : Fin n → Bool =>
            (fun x => G (n + 1) k (Function.update x p true)) (y ∘ del n k hk)) = G n (k + 1) := by
          funext y; exact G_del_true n k hk y
        rw [e] at h''
        have := ih (d - 2) (by omega) (by omega) (k + 1) n s' (by omega) h''
        omega

 
def path (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (∃ i j : Fin n, i.val + 1 = j.val ∧ x i = true ∧ x j = true)

theorem path_eq_G (n : ℕ) : path n = G n 0 := by
  funext x
  simp [path, G]

theorem path_lower (n s : ℕ) (h : HasCircuitSize n (path n) s) : n + n / 2 ≤ s + 2 := by
  by_cases hn : n ≤ 1
  · have : n / 2 = 0 := by omega
    omega
  · rw [path_eq_G] at h
    exact G_lower n (by omega) 0 n s (by omega) h

end PEqualNP.Outside.L_meta_191_PathLib.PathSize

namespace PEqualNP.Outside.Size191
open CircuitLowerBounds MetaComplexity PEqualNP.Outside.L_meta_191_PathLib.PathSize

theorem size_five (C : Circuit) (hm : IsMinimalCircuit 5 C)
    (hc : circuitFun 5 C = (fun x : Fin 5 → Bool =>
      decide (∃ i j : Fin 5, i.val+1=j.val ∧ x i=true ∧ x j=true))) : C.size = 5 := by
  let D : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[2,4]⟩,⟨.and,[1,5]⟩,⟨.and,[3,6]⟩,⟨.or,[7,8]⟩],9⟩
  have hf : FanInTwo D := by simp [D,FanInTwo]
  have he : circuitFun 5 D = path 5 := funext (by decide : ∀ x, circuitFun 5 D x = path 5 x)
  have upper := hm.2 D hf (he.trans hc.symm)
  change C.size ≤ 5 at upper
  have lower := path_lower 5 C.size ⟨C,hm.1,le_rfl,congrFun hc⟩
  omega

end PEqualNP.Outside.Size191

namespace PEqualNP.Outside.Tree191

inductive Tree where
  | leaf (i : Fin 5)
  | node (op : Bool) (a b : Tree)

def leaves : Tree → Multiset (Fin 5)
  | .leaf i => {i}
  | .node _ a b => leaves a + leaves b

def full : Multiset (Fin 5) := {0,1,2,2,3,4}
def targets : List ℕ := [4210752250,4294963440,3368601800,4278251520,4291360968]
def lit (i : Fin 5) : ℕ := [2863311530,3435973836,4042322160,4278255360,4294901760][i.val]!
def combine (op : Bool) (x y : ℕ) := if op then x &&& y else x ||| y
def value : Tree → ℕ
  | .leaf i => lit i
  | .node op a b => combine op (value a) (value b)
def nodes : Tree → List ℕ
  | .leaf _ => []
  | .node op a b => combine op (value a) (value b) :: nodes a ++ nodes b

private def bit (x : ℕ) : ℕ := match x with
  | 4210752250 => 1 | 4294963440 => 2 | 3368601800 => 4 | 4278251520 => 8 | 4291360968 => 16 | _ => 0
private def hits : Tree → ℕ
  | .leaf _ => 0
  | .node op a b => bit (combine op (value a) (value b)) ||| hits a ||| hits b

private lemma hit_mem (t : Tree) (i : Fin 5) (h : (hits t).testBit i.val = true) :
    targets[i.val]! ∈ nodes t := by
  induction t with
  | leaf v => simp [hits] at h
  | node op a b ia ib =>
    simp only [hits,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with (h|h)|h
    · apply List.mem_cons.mpr; left
      generalize combine op (value a) (value b) = v at *
      unfold bit at h
      split at h <;> fin_cases i <;> simp_all [targets] <;> revert h <;> decide
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ia h))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ib h))

private def weight (i : Fin 5) : ℕ := [1,2,4,12,24][i.val]!
private def idx (b : Multiset (Fin 5)) := (b.map weight).sum

private def table : ℕ → List ℕ
  | 0 => []
  | 1 => [91625968960]
  | 2 => [109951162752]
  | 3 => [73300775168,128276356544]
  | 4 => [129354309120]
  | 5 => [86236206080,134744072001]
  | 6 => [103483447296,135822024576]
  | 7 => [68988964864,90548016384,107795257605,120730688512,126120451392,127198403968,133666119424,136899977152,136899977153]
  | 8 => [129354309120]
  | 9 => [86236206080,129354309120,129354309121,134744072001]
  | 10 => [103483447296,129354309120,135822024576]
  | 11 => [68988964864,86236206080,90548016384,103483447296,103483447297,103483447301,107795257605,120730688512,126120451392,127198403968,129354309120,129354309121,133666119424,133666119425,133666119429,134744072001,135822024576,135822024577,136899977152,136899977153]
  | 12 => [136904171520]
  | 13 => [91269447680,137260692800]
  | 14 => [109523337216,137331997056]
  | 15 => [73015558144,91554664704,109808554240,127777226752,128133748032,128205052288,137189388544,137403301312]
  | 16 => [128850984960,137407495680]
  | 17 => [85900656640,91604997120,129186534400,134219776001,134576297280,134723100160,137239720960,137428467520,137428467521]
  | 18 => [103080787968,109925996544,129253644288,135293534208,135721359744,135796858368,137306830848,137432661888]
  | 19 => [68720525312,73283997696,86169096192,90195689472,90480906496,90531238912,91537887232,91621774592,103349227520,107375820801,107375820805,107661037824,107778480128,109791776768,109942774016,109942774017,120260919296,120596468736,120663578624,125629710336,125986231616,126032369664,126703468544,127039017984,127131294080,128246995968,128267967808,128272162176,129119424512,129320754176,133146017792,133431234816,133649341952,134639212801,134710517056,134739877632,135645861120,135788469632,135813635840,136367292416,136367292417,136723813696,136795117953,136866422208,136870616576,136891588416,136891588417,136895782784,137172611072,137256498432,137323608325,137373940736,137394912576,137399106944,137424273152,137436856256,137436856257]
  | 20 => [128850984960,129354309120,137407495680]
  | 21 => [85900656640,86236206080,91604997120,128850984960,128850984961,129186534400,129354309120,129354309121,134219776001,134576297280,134723100160,134723100161,134744072001,137239720960,137407495680,137407495681,137428467520,137428467521]
  | 22 => [103080787968,103483447296,109925996544,128850984960,129253644288,129354309120,135293534208,135721359744,135796858368,135822024576,137306830848,137407495680,137432661888]
  | 23 => [68720525312,68988964864,73283997696,85900656640,86169096192,86236206080,90195689472,90480906496,90531238912,90548016384,91537887232,91604997120,91621774592,103080787968,103080787969,103080787973,103349227520,103483447296,103483447297,107375820801,107375820805,107661037824,107778480128,107778480129,107778480133,107795257605,109791776768,109925996544,109925996545,109942774016,109942774017,120260919296,120596468736,120663578624,120730688512,125629710336,125986231616,126032369664,126099479552,126120451392,126703468544,127039017984,127131294080,127173237760,127198403968,128246995968,128267967808,128272162176,128850984960,128850984961,129119424512,129186534400,129253644288,129253644289,129253644293,129320754176,129354309120,129354309121,133146017792,133146017793,133146017797,133431234816,133498344704,133565454593,133565454597,133649341952,133649341953,133649341957,133666119424,134219776001,134576297280,134622435329,134639212801,134710517056,134723100160,134739877632,134739877633,134744072001,135293534208,135293534209,135629083648,135645861120,135721359744,135721359745,135788469632,135796858368,135796858369,135813635840,135813635841,135822024576,135822024577,136367292416,136367292417,136723813696,136795117953,136866422208,136870616576,136870616577,136891588416,136891588417,136895782784,136895782785,136899977152,136899977153,137172611072,137239720960,137256498432,137306830848,137306830849,137306830853,137323608325,137373940736,137394912576,137399106944,137407495680,137407495681,137424273152,137424273153,137424273157,137428467520,137428467521,137432661888,137432661889,137436856256,137436856257]
  | 24 => [137436856320]
  | 25 => [91624570880,137438254400]
  | 26 => [109949485056,137438534016]
  | 27 => [73299656704,91625689344,109950603520,128274399232,128275797312,128276076928,137437974784,137438813632]
  | 28 => [129352335360,137438830082]
  | 29 => [86234890240,91625886722,129353651200,134742016001,134743414080,134743989760,137438172160,137438912320,137438912321,137438912322]
  | 30 => [103481868288,109951064066,129353914368,135819952128,135821629824,135821925888,137438435328,137438928768,137438928770]
  | 31 => [68987912192,73300709378,86235942912,90546634752,90547753216,90547950592,91625623552,91625952512,91625952514,103482920960,107793612801,107793612805,107794731264,107795191808,109950537728,109951129856,109951129857,109951129858,120728846336,120730162176,120730425344,126118526976,126119925056,126120105984,127196463104,127197778944,127198140800,128276241410,128276323650,128276340098,129353388032,129354177536,133664079872,133665198336,133666053632,134743660801,134743940416,134744055552,135821333760,135821892992,135821991680,136897888256,136897888257,136899286336,136899565953,136899845568,136899862016,136899944256,136899944257,136899960704,137437908992,137438237952,137438501125,137438698496,137438780736,137438797184,137438895872,137438895874,137438945216,137438945217,137438945218]
  | 32 => [129352335360,129354309120,129354309122,137438830082]
  | 33 => [86234890240,86236206080,86236206082,91625886722,129352335360,129352335361,129353651200,129354309120,129354309121,129354309122,134742016001,134743414080,134743989760,134743989761,134743989762,134743989763,134744072001,134744072003,137438172160,137438830082,137438830083,137438912320,137438912321,137438912322,137438912323]
  | 34 => [103481868288,103483447296,103483447298,109951064066,129352335360,129353914368,129354309120,129354309122,135819952128,135821629824,135821925888,135821925890,135822024576,135822024578,137438435328,137438830082,137438928768,137438928770]
  | 35 => [68987912192,68988964864,68988964866,73300709378,86234890240,86235942912,86236206080,86236206082,90546634752,90547753216,90547950592,90547950594,90548016384,90548016386,91625623552,91625886722,91625952512,91625952514,103481868288,103481868289,103481868293,103482920960,103483447296,103483447297,103483447298,107793612801,107793612805,107794731264,107795191808,107795191809,107795191810,107795191811,107795191815,107795257605,107795257607,109950537728,109951064066,109951064067,109951129856,109951129857,109951129858,109951129859,120728846336,120730162176,120730425344,120730688512,120730688514,126118526976,126119925056,126120105984,126120369154,126120451392,126120451394,127196463104,127197778944,127198140800,127198305282,127198403968,127198403970,128276241410,128276323650,128276340098,129352335360,129352335361,129353388032,129353651200,129353914368,129353914369,129353914373,129354177536,129354309120,129354309121,129354309122,133664079872,133664079873,133664079877,133665198336,133665461504,133665724673,133665724677,133666053632,133666053633,133666053634,133666053637,133666119424,133666119426,134742016001,134743414080,134743595009,134743660801,134743940416,134743989760,134744055552,134744055553,134744055554,134744055555,134744072001,134744072003,135819952128,135819952129,135821267968,135821333760,135821629824,135821629825,135821892992,135821925888,135821925889,135821991680,135821991681,135821991682,135822024576,135822024577,135822024578,136897888256,136897888257,136899286336,136899565953,136899845568,136899862016,136899862017,136899862018,136899862019,136899944256,136899944257,136899944258,136899944259,136899960704,136899960705,136899960706,136899960707,136899977152,136899977153,136899977154,136899977155,137437908992,137438172160,137438237952,137438435328,137438435329,137438435333,137438501125,137438698496,137438780736,137438797184,137438830082,137438830083,137438895872,137438895873,137438895874,137438895877,137438895879,137438912320,137438912321,137438912322,137438928768,137438928769,137438928770,137438928771,137438945216,137438945217,137438945218,137438945219]
  | 36 => [136902082560,137438945280]
  | 37 => [91268055040,91625963520,136903475200,137258598400,137259996480,137260687360,137438248960,137438950720]
  | 38 => [109521666048,109951156224,136903753728,137329901568,137331579264,137331990528,137438527488,137438951808]
  | 39 => [73014444032,73300770816,91269169152,91553267712,91554386176,91554660352,91625684992,91625967872,109522780160,109806878720,109807997184,109808549888,109950599168,109951160576,127775277056,127776669696,127776948224,128131792896,128133190976,128133464064,128203096064,128204488704,128204773760,128276348928,128276354368,128276355456,136903196672,136904032256,137187295232,137188413696,137189384192,137260273920,137260553536,137260691712,137331298560,137331857792,137331994880,137401204736,137402602816,137402882432,137403162048,137403293696,137403299136,137403300224,137437970432,137438253312,137438531840,137438806016,137438811456,137438812544,137438949632,137438952896]
  | 40 => [128849018880,129354301440,136904048650,137405399040,137407372800,137407488000,137438822400,137438952960,137438952962]
  | 41 => [85899345920,86236200960,91269365762,91269365770,91603599360,91604915200,91604992000,91625881600,91625968640,91625968642,128850329600,129184563200,129185879040,129186529280,129353646080,129354306560,134217728001,134219120640,134219694080,134574243840,134575641920,134576209920,134721044480,134722437120,134723018240,134744064001,134744069440,134744071680,136903393280,136904130560,136904130561,136904130562,137237626880,137238942720,137239715840,137260569602,137260651850,137260692482,137406796800,137407454720,137407493120,137426370560,137426370561,137427768640,137428344320,137428426560,137428426561,137428459521,137428464960,137428467200,137438167040,137438254080,137438827520,137438904321,137438909760,137438912000,137438912002,137438950400,137438953280,137438953281,137438953282]
  | 42 => [103079215104,103483441152,109523238914,109523238922,109924319232,109925898240,109925990400,109951057920,109951162368,109951162370,128850591744,129251672064,129253251072,129253638144,129353908224,129354307584,135291469824,135293140992,135293435904,135719288832,135720966528,135721254912,135794786304,135796457472,135796760064,135822016512,135822023040,135822024192,136903655424,136904146944,136904146946,137304735744,137306314752,137306824704,137331873794,137331972490,137331996674,137407076352,137407471104,137407494144,137430564864,137432242560,137432538624,137432637312,137432653824,137432660352,137432661504,137438429184,137438533632,137438828544,137438920704,137438927232,137438928384,137438928386,137438951424,137438953344,137438953346]
  | 43 => [68719476736,68988960768,73015492610,73015492618,73282879488,73283932160,73283993600,73300705280,73300774912,73300774914,85900394496,86167781376,86168834048,86169092096,86235938816,86236205056,90194313216,90195427328,90195623936,90479525888,90480644352,90480836608,90529857536,90530971648,90531173376,90548011008,90548015360,90548016128,91269103616,91269431296,91269431298,91536490496,91537543168,91537883136,91554582530,91554648330,91554664450,91604717568,91604980736,91604996096,91620376576,91621495040,91621692416,91621758208,91621769216,91621773568,91621774336,91625619456,91625689088,91625885696,91625947136,91625951488,91625952256,91625952258,91625967616,91625968896,91625968898,103080263680,103347650560,103348703232,103349223424,103482916864,103483445248,107374182401,107374182405,107375296512,107375755264,107659395072,107660513536,107660967936,107776835584,107777949696,107778414592,107795251201,107795251205,107795255552,107795257344,109522714624,109523304448,109523304449,109523304450,109790101504,109791154176,109791772672,109808455682,109808521482,109808553986,109925437440,109925963776,109925994496,109941096448,109941096449,109942214912,109942675456,109942741248,109942741249,109942767617,109942771968,109942773760,109950533632,109950603264,109951062016,109951123457,109951127808,109951129600,109951129602,109951160320,109951162624,109951162625,109951162626,120259084288,120260395008,120260657152,120594628608,120595944448,120596201472,120661737472,120663048192,120663316480,120730681344,120730686464,120730687488,125627793408,125629186048,125629366272,125984309248,125985707328,125985882112,126030446592,126031839232,126032025600,126120443904,126120449344,126120450048,126701535232,126702845952,126703206400,127037079552,127038395392,127038750720,127129354240,127130664960,127131031936,127198396416,127198401536,127198402944,127777112066,127777112074,127777193986,127777210370,128133633026,128133715266,128133715274,128133731330,128204937218,128205019138,128205035906,128205035914,128245039104,128246436864,128246716416,128246881280,128246988800,128266010624,128267408704,128267687936,128267935040,128267965760,128270204928,128271602688,128271882624,128272145792,128272161152,128276234240,128276321600,128276339072,128276356096,128276356098,128276356416,128276356418,128276356480,128276356482,128850067456,128850853888,129117454336,129118507008,129119420416,129186140160,129186403328,129186533376,129252986880,129253513216,129253642240,129318780928,129320096768,129320359936,129320623104,129320747008,129320752128,129320753152,129353383936,129353650176,129353912320,129354170368,129354175488,129354176512,129354305536,129354308608,133143986176,133145100288,133145952256,133429198848,133430317312,133431164928,133647302656,133648416768,133649276416,133666111488,133666115840,133666119168,134219366401,134219644928,134219759616,134575886592,134576166208,134576279808,134637158401,134638555392,134638803201,134639130624,134639206401,134708461568,134709859648,134710385984,134710433792,134710515008,134722689024,134722967552,134723083776,134737821696,134739218688,134739795456,134739861248,134739877376,134743654401,134743938368,134744055296,134744070401,134744071488,134744071936,135292846080,135293403136,135293501440,135643791360,135645172992,135645466880,135645762560,135645855744,135720669440,135721228672,135721324800,135786397696,135788075392,135788338560,135788368896,135788468608,135796167680,135796724736,135796825600,135811563520,135813239040,135813537280,135813603072,135813635584,135821328384,135821891968,135821991424,135822021888,135822024064,135822024448,136365211648,136365211649,136366604288,136366882817,136367161344,136367177728,136367259648,136367259649,136367276032,136721727488,136723125568,136723682624,136723780928,136723791872,136793030657,136794708353,136794986880,136795078657,136795101568,136864333824,136865731904,136866011520,136866291136,136866299904,136866387264,136866404736,136868528128,136870477824,136870501888,136870583808,136870600192,136889499648,136889499649,136890897728,136891170817,136891454784,136891473408,136891555648,136891555649,136891571712,136893693952,136895086592,136895371648,136895650176,136895667712,136895749632,136895766400,136899969024,136899969025,136899974464,136899975553,136899976640,136899976704,136899977024,136899977025,136899977088,136903131136,136903458816,136903720965,136903917568,136903999488,136904015872,136904114176,136904114178,136904163328,136904163329,136904163330,137170518016,137171570688,137172606976,137189265410,137189331210,137189388290,137239302144,137239565312,137239719936,137254404096,137255785728,137256493056,137256497408,137256498176,137260175360,137260520768,137260668160,137260668162,137260684608,137260684610,137260691456,137260692736,137260692738,137306132480,137306658816,137306828800,137321512965,137323157765,137323601921,137323601925,137323606272,137323608064,137331216384,137331841408,137331955968,137331955969,137331955970,137331988864,137331988865,137331988866,137331994624,137331996928,137331996929,137331996930,137371844608,137373686784,137373933568,137373938688,137373939712,137392816128,137394214208,137394395136,137394740544,137394905088,137394910528,137394911232,137397010432,137398326272,137398688128,137398951296,137399099392,137399104512,137399105920,137403177986,137403260226,137403276674,137403293130,137403300866,137403301186,137403301250,137406517248,137407355904,137407438336,137407487488,137407492096,137407495168,137422176256,137423294720,137424150016,137424215808,137424265216,137424269568,137424272896,137428048128,137428048129,137428327744,137428442880,137428459328,137428459329,137428465921,137428467008,137428467456,137431962880,137432522112,137432620800,137432653696,137432659200,137432661376,137432661760,137434759168,137434759169,137436157248,137436436864,137436436865,137436716480,137436732928,137436815168,137436815169,137436831616,137436848064,137436848065,137436848128,137436848129,137436853568,137436854657,137436855744,137436855808,137436856128,137436856129,137436856192,137437904896,137437974528,137438171136,137438232576,137438236928,137438237696,137438253056,137438254336,137438433280,137438494721,137438494725,137438499072,137438500864,137438531584,137438533888,137438533889,137438691328,137438696448,137438697472,137438773248,137438778688,137438779392,137438789632,137438794752,137438796160,137438813184,137438813504,137438813568,137438826496,137438829568,137438887936,137438892288,137438895616,137438895618,137438910721,137438911808,137438912256,137438912258,137438926080,137438928256,137438928640,137438928642,137438937088,137438937089,137438942528,137438943617,137438944704,137438944768,137438944770,137438945088,137438945089,137438945090,137438945152,137438945154,137438949376,137438950656,137438951685,137438952448,137438952768,137438952832,137438953216,137438953218,137438953408,137438953409,137438953410]
  | 44 => [128849018880,128850984960,128850984962,128850984970,129352335360,129354301440,129354309120,129354309122,136904048650,137405399040,137407372800,137407372802,137407372810,137407488000,137407495680,137407495682,137438822400,137438830082,137438952960,137438952962]
  | 45 => [85899345920,85900656640,85900656642,85900656650,86234890240,86236200960,86236206080,86236206082,91269365762,91269365770,91603599360,91604915200,91604915202,91604915210,91604992000,91604997120,91604997122,91625881600,91625886722,91625968640,91625968642,128849018880,128849018881,128850329600,128850984960,128850984961,128850984962,129184563200,129185879040,129186529280,129186534400,129186534402,129186534410,129352335360,129352335361,129353646080,129353651200,129354301440,129354301441,129354306560,129354309120,129354309121,129354309122,134217728001,134219120640,134219694080,134219694081,134219694082,134219694083,134219694091,134219776001,134219776003,134574243840,134575641920,134576209920,134576215042,134576297280,134576297282,134576297290,134721044480,134721044481,134722437120,134722442240,134723018240,134723018241,134723018242,134723018250,134723092481,134723100160,134723100162,134742016001,134743414080,134743982081,134743989760,134744064001,134744069440,134744071680,134744071681,134744071682,134744071683,134744072001,134744072003,136903393280,136904048650,136904048651,136904130560,136904130561,136904130562,136904130563,137237626880,137238942720,137239598082,137239598090,137239715840,137239720960,137239720962,137260569602,137260651850,137260692482,137405399040,137405399041,137406714880,137406796800,137407372800,137407372801,137407454720,137407454721,137407454722,137407488000,137407488001,137407493120,137407495680,137407495681,137407495682,137426370560,137426370561,137427768640,137428344320,137428344321,137428344322,137428344323,137428426560,137428426561,137428426562,137428426570,137428426571,137428459521,137428464960,137428467200,137428467201,137428467202,137428467203,137428467520,137428467521,137428467522,137428467523,137438167040,137438172160,137438254080,137438822400,137438822401,137438827520,137438830082,137438830083,137438904321,137438909760,137438912000,137438912001,137438912002,137438912003,137438912320,137438912321,137438912322,137438950400,137438952960,137438952961,137438952962,137438952963,137438953280,137438953281,137438953282,137438953283]
  | 46 => [103079215104,103080787968,103080787970,103080787978,103481868288,103483441152,103483447296,103483447298,109523238914,109523238922,109924319232,109925898240,109925898242,109925898250,109925990400,109925996544,109925996546,109951057920,109951064066,109951162368,109951162370,128849018880,128850591744,128850984960,128850984962,129251672064,129253251072,129253638144,129253644288,129253644290,129253644298,129352335360,129353908224,129353914368,129354301440,129354307584,129354309120,129354309122,135291469824,135293140992,135293435904,135293435906,135293435914,135293534208,135293534210,135719288832,135720966528,135721254912,135721261058,135721359744,135721359746,135721359754,135794786304,135796457472,135796463616,135796760064,135796760066,135796760074,135796850688,135796858368,135796858370,135819952128,135821629824,135821918208,135821925888,135822016512,135822023040,135822024192,135822024194,135822024576,135822024578,136903655424,136904048650,136904146944,136904146946,137304735744,137306314752,137306707970,137306707978,137306824704,137306830848,137306830850,137331873794,137331972490,137331996674,137405399040,137406978048,137407076352,137407372800,137407471104,137407471106,137407488000,137407494144,137407495680,137407495682,137430564864,137432242560,137432538624,137432538626,137432637312,137432637314,137432637322,137432653824,137432660352,137432661504,137432661506,137432661888,137432661890,137438429184,137438435328,137438533632,137438822400,137438828544,137438830082,137438920704,137438927232,137438928384,137438928386,137438928768,137438928770,137438951424,137438952960,137438952962,137438953344,137438953346]
  | 47 => []
  | _ => []

private def forbidden : List ℕ := [4291357384,4292930784,4244176008,4291623048]

private def accept (i v h : ℕ) : Bool :=
  if i = 47 then !forbidden.contains v && (v != 4291360968 || h == 31) else (table i).contains (v*32+h)

private def merge (i x y : ℕ) : Bool :=
  [false,true].all fun op =>
    let v := combine op (x/32) (y/32)
    accept i v (bit v ||| (x%32) ||| (y%32))

private def bag (i : ℕ) : Multiset (Fin 5) :=
  (List.replicate (i%2) 0 ++ List.replicate (i/2%2) 1 ++ List.replicate (i/4%3) 2 ++
   List.replicate (i/12%2) 3 ++ List.replicate (i/24%2) 4 : List (Fin 5))

private lemma subs : ∀ b ∈ full.powerset, idx b < 48 ∧ bag (idx b) = b := by decide +kernel
private lemma checkLeaf : ∀ i : Fin 5, accept (idx {i}) (lit i) 0 = true := by decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private lemma certify : ∀ i j : Fin 47, bag i.val + bag j.val ≤ full →
    (table i.val).all (fun x => (table j.val).all (fun y => merge (i.val+j.val) x y)) = true := by
  decide +kernel

private lemma hit_small (t : Tree) : hits t < 2^5 := by
  induction t with
  | leaf i => simp [hits]
  | node op a b ha hb =>
    apply Nat.or_lt_two_pow _ hb
    apply Nat.or_lt_two_pow _ ha
    unfold bit
    split <;> decide

private lemma sum_idx (a b : Multiset (Fin 5)) : idx (a+b) = idx a + idx b := by simp [idx]

private lemma nonempty (t : Tree) : leaves t ≠ 0 := by
  induction t <;> simp_all [leaves]

private lemma id_full : idx full = 47 := by decide
private lemma bag_full : bag 47 = full := by decide

private lemma sound (t : Tree) (h : leaves t ≤ full) : accept (idx (leaves t)) (value t) (hits t) = true := by
  induction t with
  | leaf i => exact checkLeaf i
  | node op a b ha hb =>
    change leaves a + leaves b ≤ full at h
    have hA : leaves a ≤ full := (Multiset.le_add_right _ _).trans h
    have hB : leaves b ≤ full := (Multiset.le_add_left _ _).trans h
    obtain ⟨la,ba⟩ := subs _ (Multiset.mem_powerset.mpr hA)
    obtain ⟨lb,bb⟩ := subs _ (Multiset.mem_powerset.mpr hB)
    have small {a b : Tree} (hh : leaves a + leaves b ≤ full)
        (bl : bag (idx (leaves a)) = leaves a) (hl : idx (leaves a) < 48) : idx (leaves a) < 47 := by
      by_contra! hn
      have he : idx (leaves a) = 47 := by omega
      rw [he,bag_full] at bl
      rw [← bl] at hh
      have hz : (leaves b).card = 0 := by have hx := Multiset.card_le_card hh; rw [Multiset.card_add] at hx; omega
      exact nonempty b (Multiset.card_eq_zero.mp hz)
    have ia := small h ba la
    have ib := small (a:=b) (b:=a) (by simpa [add_comm] using h) bb lb
    have cert := certify ⟨_,ia⟩ ⟨_,ib⟩ (by simpa only [ba,bb] using h)
    have ax := ha hA
    have bx := hb hB
    simp only [accept,ite_eq_right (show idx (leaves a) ≠ 47 by omega),List.contains_iff_mem] at ax
    simp only [accept,ite_eq_right (show idx (leaves b) ≠ 47 by omega),List.contains_iff_mem] at bx
    have cm := List.all_eq_true.mp (List.all_eq_true.mp cert _ ax) _ bx
    have co := List.all_eq_true.mp cm op (by cases op <;> simp)
    have ah := hit_small a
    have bh := hit_small b
    change hits a < 32 at ah
    change hits b < 32 at bh
    change accept _ (combine op (((value a)*32+hits a)/32) (((value b)*32+hits b)/32)) _ = true at co
    have div (v h : ℕ) (hh : h < 32) : (v*32+h)/32 = v := by omega
    have md (v h : ℕ) (hh : h < 32) : (v*32+h)%32 = h := by omega
    simp only [div _ _ ah,div _ _ bh,md _ _ ah,md _ _ bh] at co
    simpa only [leaves,sum_idx,value,hits] using co

theorem classify (t : Tree) (hl : leaves t = full) (hv : value t = 4291360968) :
    ∀ v ∈ targets, v ∈ nodes t := by
  have h := sound t (le_of_eq hl)
  rw [hl,id_full,hv] at h
  have hh : hits t = 31 := by simpa [accept, forbidden] using h
  intro v hm
  have : ∃ i : Fin 5, targets[i.val]! = v :=
    (by decide : ∀ z ∈ targets, ∃ j : Fin 5, targets[j.val]! = z) v hm
  obtain ⟨i,rfl⟩ := this
  apply hit_mem _ i
  rw [hh]
  exact (by decide : ∀ j : Fin 5, (31 : ℕ).testBit j.val = true) i

private def swappedGoal (d : Fin 5) : ℕ := [4291357384, 4292930784, 4291360968, 4244176008, 4291623048][d.val]!

private def swapLeaf (d : Fin 5) (i : Fin 5) : Fin 5 := if i=d then 2 else if i=2 then d else i

private def rename (d : Fin 5) : Tree → Tree
  | .leaf i => .leaf (swapLeaf d i)
  | .node op a b => .node op (rename d a) (rename d b)

private lemma renLeaves (d : Fin 5) (t : Tree) :
    leaves (rename d t) = (leaves t).map (swapLeaf d) := by
  induction t <;> simp_all [leaves, rename]

def allInputs : Multiset (Fin 5) := {0,1,2,3,4}

private def swapRow (d : Fin 5) (r : Fin 32) : Fin 32 :=
  Fin.ofNat 32 (if r.val.testBit d.val = r.val.testBit 2 then r.val else r.val ^^^ (2^d.val) ^^^ 4)

private lemma renameBit (d : Fin 5) (t : Tree) (r : Fin 32) :
    (value (rename d t)).testBit r.val = (value t).testBit (swapRow d r).val := by
  induction t with
  | leaf i =>
    exact (by decide : ∀ e j : Fin 5, ∀ s : Fin 32,
      (lit (swapLeaf e j)).testBit s.val = (lit j).testBit (swapRow e s).val) d i r
  | node op a b ha hb =>
    cases op <;> simp_all [value,rename,combine,Nat.testBit_and,Nat.testBit_or]

private lemma valueBound (t : Tree) : value t < 2^32 := by
  induction t with
  | leaf i => exact (by decide : ∀ j : Fin 5, lit j < 2^32) i
  | node op a b ha hb =>
    cases op
    · exact Nat.or_lt_two_pow ha hb
    · exact Nat.and_lt_two_pow _ hb

private lemma rename_goal (d : Fin 5) (t : Tree) (hv : value t = 4291360968) :
    value (rename d t) = swappedGoal d := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 32
  · have e := renameBit d t ⟨k,hk⟩
    rw [hv] at e
    exact e.trans ((by decide : ∀ d : Fin 5, ∀ s : Fin 32,
      (4291360968 : ℕ).testBit (swapRow d s).val = (swappedGoal d).testBit s.val) d ⟨k,hk⟩)
  · have p : 2^32 ≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) (by omega)
    have h := (by decide : ∀ d : Fin 5, swappedGoal d < 2^32) d
    rw [Nat.testBit_lt_two_pow ((valueBound _).trans_le p),Nat.testBit_lt_two_pow (h.trans_le p)]

theorem classifyAny (t : Tree) (d : Fin 5) (hl : leaves t = allInputs + {d})
    (hv : value t = 4291360968) : d = 2 ∧ ∀ v ∈ targets, v ∈ nodes t := by
  have hr : leaves (rename d t) = full := by
    rw [renLeaves,hl]
    exact (by decide : ∀ e : Fin 5, (allInputs + {e}).map (swapLeaf e) = full) d
  have hs := sound (rename d t) hr.le
  rw [hr,id_full,rename_goal d t hv] at hs
  have hd : d = 2 := by
    by_contra h
    have hf := (by decide : ∀ e : Fin 5, e ≠ 2 → forbidden.contains (swappedGoal e) = true) d h
    simp [accept] at hs
    exact hs.1 (List.contains_iff_mem.mp hf)
  refine ⟨hd,classify t ?_ hv⟩
  rw [hd] at hl
  exact hl.trans (by decide)

end PEqualNP.Outside.Tree191
namespace PEqualNP.Outside.L_meta_191_aux

/-- Every internal use cancels its producing gate. The extra raw operand is counted twice. -/
theorem wire_balance {M : Type*} [AddCancelCommMonoid M] (W : ℕ → M) (fee : Fin 5 → M)
    (a b : Fin 5 → ℕ) (extra : ℕ)
    (ports : (([a 0,b 0,a 1,b 1,a 2,b 2,a 3,b 3,a 4,b 4] : List ℕ) : Multiset ℕ)
      = Multiset.range 9 + {extra})
    (step : ∀ i : Fin 5, W (5+i.val) = W (a i) + W (b i) + fee i) :
    W 9 = (W 0 + W 1 + W 2 + W 3 + W 4 + W extra) +
      (fee 0 + fee 1 + fee 2 + fee 3 + fee 4) := by
  have ports' := congrArg (fun s : Multiset ℕ => (s.map W).sum) ports
  have r : Multiset.range 9 = (([0,1,2,3,4,5,6,7,8] : List ℕ) : Multiset ℕ) := by decide
  simp only [r,Multiset.map_add,Multiset.sum_add,Multiset.map_singleton,Multiset.sum_singleton,
    Multiset.map_coe,Multiset.sum_coe,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at ports'
  have exchange : W 5 + W 6 + W 7 + W 8 + W 9 =
      (W 0 + W 1 + W 2 + W 3 + W 4 + W 5 + W 6 + W 7 + W 8 + W extra) +
      (fee 0 + fee 1 + fee 2 + fee 3 + fee 4) := by
    have s0 : W 5 = _ := step 0
    have s1 : W 6 = _ := step 1
    have s2 : W 7 = _ := step 2
    have s3 : W 8 = _ := step 3
    have s4 : W 9 = _ := step 4
    calc
      _ = (W (a 0) + (W (b 0) + (W (a 1) + (W (b 1) + (W (a 2) + (W (b 2) +
          (W (a 3) + (W (b 3) + (W (a 4) + W (b 4)))))))))) +
          (fee 0 + fee 1 + fee 2 + fee 3 + fee 4) := by rw [s0,s1,s2,s3,s4]; abel
      _ = _ := by rw [ports']; abel
  apply add_left_cancel (a := W 5 + W 6 + W 7 + W 8)
  rw [exchange]; abel
end PEqualNP.Outside.L_meta_191_aux
namespace PEqualNP.Outside.L_meta_191_aux
open CircuitLowerBounds
open PEqualNP.Outside.Tree191

private def binaryGate (o : Bool) (a b : ℕ) : Gate := ⟨if o then .and else .or,[a,b]⟩

private def unfoldWire (o : Fin 5 → Bool) (a b : Fin 5 → ℕ)
    (ha : ∀ i : Fin 5, a i < 5+i.val) (hb : ∀ i : Fin 5, b i < 5+i.val) (w : ℕ) : Tree :=
  if hw : w < 5 then .leaf ⟨w,hw⟩
  else if hs : w < 10 then
    let i : Fin 5 := ⟨w-5,by omega⟩
    .node (o i) (unfoldWire o a b ha hb (a i)) (unfoldWire o a b ha hb (b i))
  else .leaf 0
termination_by w
decreasing_by
  all_goals first | have hh := ha i; dsimp [i] at hh; omega | have hh := hb i; dsimp [i] at hh; omega

private theorem uleaf (o a b ha hb) (i : Fin 5) : unfoldWire o a b ha hb i.val = .leaf i := by
  rw [unfoldWire, dite_eq_left i.isLt]

private theorem unode (o a b ha hb) (i : Fin 5) :
    unfoldWire o a b ha hb (5+i.val) = .node (o i)
      (unfoldWire o a b ha hb (a i)) (unfoldWire o a b ha hb (b i)) := by
  rw [unfoldWire, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

private theorem lookupRange (f : ℕ → ℕ) {k i : ℕ} (h : i < k) :
    ((List.range k).map f).getD i 0 = f i := by simp [List.getD_eq_getElem?_getD,h]

private theorem assembled (o : Fin 5 → Bool) (a b : Fin 5 → ℕ) (ha hb)
    (k : ℕ) (hk : k ≤ 5) :
    wireMasks ((List.range k).map (fun j => binaryGate (o (Fin.ofNat 5 j)) (a (Fin.ofNat 5 j)) (b (Fin.ofNat 5 j)))) =
    (List.range (5+k)).map (fun j => value (unfoldWire o a b ha hb j)) := by
  induction k with
  | zero =>
    change maskInputs = (List.range 5).map _
    rw [show List.range 5 = [0,1,2,3,4] by decide]
    simp only [List.map_cons,List.map_nil]
    rw [uleaf o a b ha hb ⟨0,by decide⟩, uleaf o a b ha hb ⟨1,by decide⟩, uleaf o a b ha hb ⟨2,by decide⟩, uleaf o a b ha hb ⟨3,by decide⟩, uleaf o a b ha hb ⟨4,by decide⟩]
    rfl
  | succ k ih =>
    let i : Fin 5 := ⟨k,by omega⟩
    have hi : Fin.ofNat 5 k = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    specialize ih (by omega)
    let f := fun j => value (unfoldWire o a b ha hb j)
    let program := (List.range k).map (fun j => binaryGate (o (Fin.ofNat 5 j)) (a (Fin.ofNat 5 j)) (b (Fin.ofNat 5 j)))
    change wireMasks program = (List.range (5+k)).map f at ih
    rw [List.range_succ, List.map_append]
    rw [wireMasks, List.foldl_append]
    change wireMasks program ++ [gateMask (wireMasks program) (binaryGate (o (Fin.ofNat 5 k)) (a (Fin.ofNat 5 k)) (b (Fin.ofNat 5 k)))] = _
    rw [ih, hi, show 5+(k+1) = (5+k)+1 by omega, List.range_succ,List.map_append]
    congr 1
    change [gateMask ((List.range (5+k)).map f) (binaryGate (o i) (a i) (b i))] = [f (5+i.val)]
    have hai : a i < 5+k := ha i
    have hbi : b i < 5+k := hb i
    have q : f (5+i.val) = combine (o i) (f (a i)) (f (b i)) := by simp [f,unode,value]
    rw [q]
    cases e : o i <;> simp [gateMask,binaryGate,combine,lookupRange f hai,lookupRange f hbi,
      -List.getD_eq_getElem?_getD]

private theorem generatedNodes (o a b ha hb) (w : ℕ) (hw : w < 10) :
    ∀ m ∈ nodes (unfoldWire o a b ha hb w), ∃ j : Fin 5, value (unfoldWire o a b ha hb (5+j.val)) = m := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases low : w < 5
    · rw [uleaf o a b ha hb ⟨w,low⟩]
      simp [nodes]
    · let i : Fin 5 := ⟨w-5,by omega⟩
      have he : 5+i.val = w := by dsimp [i]; omega
      have st := unode o a b ha hb i
      rw [he] at st
      intro m hm
      rw [st] at hm
      change m ∈ _ :: (_ ++ _) at hm
      rcases List.mem_cons.mp hm with h|h
      · exact ⟨i, by simpa only [unode,value] using h.symm⟩
      · rcases List.mem_append.mp h with h|h
        · exact ih _ (he ▸ ha i) (by have := ha i; omega) _ h
        · exact ih _ (he ▸ hb i) (by have := hb i; omega) _ h

/-- Unfold the five gates at their actual wire addresses.  The gate-port balance
counts exactly the six leaves of the output tree. -/
theorem expand191 (gs : List Gate) (hlen : gs.length = 5)
    (hb : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (hsafe : ∀ j g, gs[j]? = some g → ∀ k ∈ g.inputs, k < 5+j)
    (d : Fin 5) (hports : (ports gs : Multiset ℕ) = Multiset.range 9 + {d.val})
    (hout : (wireMasks gs).getD 9 0 = 4291360968) :
    ∀ m ∈ Tree191.targets, m ∈ (wireMasks gs).drop 5 := by
  let G (i : Fin 5) := gs[i.val]'(by omega)
  have hget (i : Fin 5) : gs[i.val]? = some (G i) := List.getElem?_eq_getElem (by omega)
  have raw (i : Fin 5) : ∃ op : Bool, ∃ a b : ℕ, G i = binaryGate op a b := by
    obtain ⟨hop,hl⟩ := hb (G i) (List.getElem_mem _)
    generalize G i = g at hop hl ⊢
    obtain ⟨gop,ids⟩ := g
    change gop = .and ∨ gop = .or at hop
    change ids.length = 2 at hl
    rcases List.length_eq_two.mp hl with ⟨a,b,rfl⟩
    rcases hop with rfl|rfl
    · exact ⟨true,a,b,rfl⟩
    · exact ⟨false,a,b,rfl⟩
  choose op a b hg using raw
  have pg (i : Fin 5) : gs[i.val]? = some (binaryGate (op i) (a i) (b i)) := (hget i).trans (congrArg some (hg i))
  have ha (i : Fin 5) : a i < 5+i.val := hsafe _ _ (pg i) _ (by simp [binaryGate])
  have hbb (i : Fin 5) : b i < 5+i.val := hsafe _ _ (pg i) _ (by simp [binaryGate])
  let W := unfoldWire op a b ha hbb
  have gl : gs = (List.range 5).map (fun j => binaryGate (op (Fin.ofNat 5 j)) (a (Fin.ofNat 5 j)) (b (Fin.ofNat 5 j))) := by
    apply List.ext_getElem (by simp [hlen])
    intro j hj hj'
    let i : Fin 5 := ⟨j,by omega⟩
    have eqi : Fin.ofNat 5 j = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    simp only [List.getElem_map,List.getElem_range,eqi]
    exact hg i
  have mlist : wireMasks gs = (List.range 10).map (fun i => value (W i)) := by
    rw [gl]
    exact assembled op a b ha hbb 5 (by decide)
  have htree : value (W 9) = 4291360968 := by
    simpa only [mlist,lookupRange _ (by decide : 9 < 10)] using hout
  have ports' : (([a 0,b 0,a 1,b 1,a 2,b 2,a 3,b 3,a 4,b 4] : List ℕ) : Multiset ℕ) =
      Multiset.range 9 + {d.val} := by
    rw [gl] at hports
    exact hports
  have st (i : Fin 5) : leaves (W (5+i.val)) = leaves (W (a i)) + leaves (W (b i)) + 0 := by
    rw [show W (5+i.val) = _ from unode op a b ha hbb i,leaves,add_zero]
  have counts := wire_balance (fun i => leaves (W i)) (fun _ => 0) a b d.val ports' st
  have hc : leaves (W 9) = allInputs + {d} := by
    rw [show W d.val = _ from uleaf op a b ha hbb d] at counts
    rw [show W 0 = _ from uleaf op a b ha hbb ⟨0,by decide⟩,
        show W 1 = _ from uleaf op a b ha hbb ⟨1,by decide⟩,
        show W 2 = _ from uleaf op a b ha hbb ⟨2,by decide⟩,
        show W 3 = _ from uleaf op a b ha hbb ⟨3,by decide⟩,
        show W 4 = _ from uleaf op a b ha hbb ⟨4,by decide⟩] at counts
    simpa [leaves,allInputs,Multiset.insert_eq_cons,Multiset.cons_add,add_assoc] using counts
  intro m hm
  have hit := (classifyAny (W 9) d hc htree).2 m hm
  obtain ⟨j,hj⟩ := generatedNodes op a b ha hbb 9 (by decide) m hit
  rw [mlist]
  change m ∈ ([5,6,7,8,9] : List ℕ).map (fun k => value (W k))
  apply List.mem_map.mpr
  refine ⟨5+j.val,?_,hj⟩
  have mem : 5+j.val ∈ ([5,6,7,8,9] : List ℕ) := by fin_cases j <;> decide
  exact mem

end PEqualNP.Outside.L_meta_191_aux

namespace PEqualNP.Outside.Short191
open CircuitLowerBounds MetaComplexity

def target (x : Fin 5 → Bool) := decide (∃ i j : Fin 5, i.val+1=j.val ∧ x i=true ∧ x j=true)
private def run (gs : List Gate) (x : Fin 5 → Bool) := (Circuit.mk gs 0).wires (List.ofFn x)
private def ports (gs : List Gate) := gs.flatMap Gate.inputs
private def op (i : Fin 3) : GateOp := ![.and,.or,.not] i
private def bits (i : ℕ) (v : Fin 5) := i.testBit v.val

private def short (a b : Fin 5) (i : Fin 3) : List Gate := [⟨op i,[a.val,b.val]⟩]
private def long (a : Fin 5) (b c : Fin 6) (i j : Fin 3) : List Gate :=
  [⟨op i,[a.val]⟩,⟨op j,[b.val,c.val]⟩]

-- Two explicit inputs distinguish the path function after each permitted prefix.
-- Their remaining usable wires agree, so no continuation can distinguish them.
private def oneData : Array ℕ := #[
  0,0,0,134,35,35,67,300,70,67,106,140,67,114,280,134,35,67,0,0,0,35,101,70,35,
  105,140,35,113,280,67,300,67,35,101,35,0,0,0,70,202,140,70,210,280,67,106,67,35,105,
  35,70,202,70,0,0,0,140,404,280,67,114,67,35,113,35,70,210,70,140,404,140,0,0,0]
private def twoData : Array ℕ := #[
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,35,101,70,
  35,101,70,35,101,70,35,105,140,35,105,140,35,105,140,35,113,280,35,113,280,35,113,280,134,
  35,67,134,35,67,3,3,67,0,0,0,0,0,0,0,0,0,35,101,35,35,101,35,35,101,
  35,0,0,0,0,0,0,0,0,0,70,202,140,70,202,140,70,202,140,70,210,280,70,210,280,
  70,210,280,67,300,67,67,300,67,67,70,67,0,0,0,0,0,0,0,0,0,35,105,35,35,
  105,35,35,105,35,70,202,70,70,202,70,70,202,70,0,0,0,0,0,0,0,0,0,140,404,
  280,140,404,280,140,404,280,67,106,67,67,106,67,67,75,67,0,0,0,0,0,0,0,0,0,
  35,113,35,35,113,35,35,113,35,70,210,70,70,210,70,70,210,70,140,404,140,140,404,140,140,
  404,140,0,0,0,0,0,0,0,0,0,67,114,67,67,114,67,67,83,67,0,0,0,0,0,
  0,0,0,0,134,35,35,134,35,35,3,3,35,67,300,70,67,300,70,67,70,70,67,106,140,
  67,106,140,67,75,140,67,114,280,67,114,280,67,83,280,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,67,300,70,67,300,70,67,300,
  70,67,106,140,67,106,140,67,106,140,67,114,280,67,114,280,67,114,280,134,35,35,134,35,35,
  3,3,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,67,300,67,67,300,67,67,300,67,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,70,202,140,70,202,140,70,202,140,70,210,280,70,210,280,70,
  210,280,35,101,35,35,101,35,35,6,35,67,106,67,67,106,67,67,106,67,0,0,0,0,0,
  0,0,0,0,70,202,70,70,202,70,70,202,70,0,0,0,0,0,0,0,0,0,140,404,280,
  140,404,280,140,404,280,35,105,35,35,105,35,35,43,35,67,114,67,67,114,67,67,114,67,0,
  0,0,0,0,0,0,0,0,70,210,70,70,210,70,70,210,70,140,404,140,140,404,140,140,404,
  140,0,0,0,0,0,0,0,0,0,35,113,35,35,113,35,35,51,35,134,35,67,134,35,67,
  3,3,67,0,0,0,0,0,0,0,0,0,35,101,70,35,101,70,35,6,70,35,105,140,35,
  105,140,35,43,140,35,113,280,35,113,280,35,51,280,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,134,35,35,134,35,35,134,35,35,0,0,0,0,0,0,0,0,0,
  67,106,140,67,106,140,67,106,140,67,114,280,67,114,280,67,114,280,67,300,70,67,300,70,70,
  67,70,134,35,67,134,35,67,134,35,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,35,105,140,35,105,140,35,105,140,35,113,280,35,113,280,35,113,280,35,101,70,
  35,101,70,6,35,70,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,67,106,67,67,106,67,67,106,67,35,105,35,35,105,35,
  35,105,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,140,404,280,140,
  404,280,140,404,280,70,202,70,70,202,70,70,12,70,67,114,67,67,114,67,67,114,67,35,113,
  35,35,113,35,35,113,35,0,0,0,0,0,0,0,0,0,140,404,140,140,404,140,140,404,140,
  0,0,0,0,0,0,0,0,0,70,210,70,70,210,70,70,86,70,67,300,67,67,300,67,70,
  67,67,35,101,35,35,101,35,6,35,35,0,0,0,0,0,0,0,0,0,70,202,140,70,202,
  140,70,12,140,70,210,280,70,210,280,70,86,280,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,134,35,35,134,35,35,134,35,35,67,300,70,67,300,70,67,300,70,0,
  0,0,0,0,0,0,0,0,67,114,280,67,114,280,67,114,280,67,106,140,67,106,140,75,67,
  140,134,35,67,134,35,67,134,35,67,0,0,0,0,0,0,0,0,0,35,101,70,35,101,70,
  35,101,70,0,0,0,0,0,0,0,0,0,35,113,280,35,113,280,35,113,280,35,105,140,35,
  105,140,43,35,140,67,300,67,67,300,67,67,300,67,35,101,35,35,101,35,35,101,35,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,70,210,280,70,210,280,70,210,280,
  70,202,140,70,202,140,12,70,140,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,67,114,67,67,114,67,67,114,67,35,113,35,
  35,113,35,35,113,35,70,210,70,70,210,70,70,210,70,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,140,404,140,140,404,140,140,24,140,67,106,67,67,106,67,75,67,
  67,35,105,35,35,105,35,43,35,35,70,202,70,70,202,70,12,70,70,0,0,0,0,0,0,
  0,0,0,140,404,280,140,404,280,140,24,280,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,134,35,35,134,35,35,134,35,35,67,300,70,67,300,70,67,300,70,67,106,
  140,67,106,140,67,106,140,0,0,0,0,0,0,0,0,0,67,114,280,67,114,280,83,67,280,
  134,35,67,134,35,67,134,35,67,0,0,0,0,0,0,0,0,0,35,101,70,35,101,70,35,
  101,70,35,105,140,35,105,140,35,105,140,0,0,0,0,0,0,0,0,0,35,113,280,35,113,
  280,51,35,280,67,300,67,67,300,67,67,300,67,35,101,35,35,101,35,35,101,35,0,0,0,
  0,0,0,0,0,0,70,202,140,70,202,140,70,202,140,0,0,0,0,0,0,0,0,0,70,
  210,280,70,210,280,86,70,280,67,106,67,67,106,67,67,106,67,35,105,35,35,105,35,35,105,
  35,70,202,70,70,202,70,70,202,70,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,140,404,280,140,404,280,24,140,280,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,67,114,67,67,114,67,83,67,67,
  35,113,35,35,113,35,51,35,35,70,210,70,70,210,70,86,70,70,140,404,140,140,404,140,24,
  140,140,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

private def okay (gs : List Gate) (v : ℕ) :=
  let x := bits (v%32)
  let y := bits (v/32)
  target x ≠ target y ∧ ∀ k : Fin (5+gs.length), k.val ∉ ports gs →
    (run gs x).getD k.val false = (run gs y).getD k.val false

set_option maxHeartbeats 5000000 in
private theorem short_ok : ∀ (a b : Fin 5) (i : Fin 3), (ports (short a b i)).Nodup →
    okay (short a b i) (oneData[(a.val*5+b.val)*3+i.val]!) := by
  intro a b
  fin_cases a <;> fin_cases b <;> unfold okay <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
private theorem long_ok : ∀ (a : Fin 5) (b c : Fin 6) (i j : Fin 3), (ports (long a b c i j)).Nodup →
    okay (long a b c i j) (twoData[(((a.val*6+b.val)*6+c.val)*3+i.val)*3+j.val]!) := by
  intro a b
  fin_cases a <;> fin_cases b <;> unfold okay <;> decide +kernel

private def execGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def agree (bad : ℕ → Prop) (w w' : List Bool) :=
  w.length = w'.length ∧ ∀ i, ¬ bad i → w.getD i false = w'.getD i false

private theorem agree_append {bad : ℕ → Prop} {w w' : List Bool}
    (ha : agree bad w w') (v : Bool) : agree bad (w++[v]) (w'++[v]) := by
  obtain ⟨hl,hv⟩ := ha
  refine ⟨by simp [hl], fun i hi => ?_⟩
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (hl ▸ h)]
    exact hv i hi
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hl]

private theorem agree_run {bad : ℕ → Prop} (gs : List Gate) {w w' : List Bool}
    (ha : agree bad w w') (avoid : ∀ g ∈ gs, ∀ j ∈ g.inputs, ¬bad j) :
    agree bad (gs.foldl execGate w) (gs.foldl execGate w') := by
  induction gs generalizing w w' with
  | nil => exact ha
  | cons g gs ih =>
    have eq : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => ha.2 i (avoid g (by simp) i hi))
    apply ih
    · unfold execGate; rw [eq]; exact agree_append ha _
    · exact fun k hk => avoid k (by simp [hk])

private theorem runlen (gs : List Gate) (w : List Bool) :
    (gs.foldl execGate w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih,execGate]; omega

private theorem fails (pre rest : List Gate) (v : ℕ) (hw : okay pre v)
    (hn : (ports (pre++rest)).Nodup) (ho : 9 ∉ ports pre)
    (hf : ∀ x, (Circuit.mk (pre++rest) 9).eval (List.ofFn x) = target x) : False := by
  let x := bits (v%32)
  let y := bits (v/32)
  have hl (z : Fin 5 → Bool) : (run pre z).length = 5+pre.length := by
    change (pre.foldl execGate (List.ofFn z)).length = _
    simp [runlen]
  have ha : agree (fun i => i ∈ ports pre) (run pre x) (run pre y) := by
    refine ⟨(hl x).trans (hl y).symm,fun i hi => ?_⟩
    by_cases right : i < 5+pre.length
    · exact hw.2 ⟨i,right⟩ hi
    · rw [List.getD_eq_default _ _ (by rw [hl]; omega),
          List.getD_eq_default _ _ (by rw [hl]; omega)]
  have hdis : (ports pre).Disjoint (ports rest) :=
    List.disjoint_of_nodup_append (by simpa [ports] using hn)
  have hfinal := agree_run rest ha (fun g hg i hi hip =>
    hdis hip (List.mem_flatMap.mpr ⟨g,hg,hi⟩))
  have hg := hfinal.2 9 ho
  have original (z : Fin 5 → Bool) : (rest.foldl execGate (run pre z)).getD 9 false = target z := by
    have H := hf z
    change ((pre++rest).foldl execGate (List.ofFn z)).getD 9 false = _ at H
    change (rest.foldl execGate (pre.foldl execGate (List.ofFn z))).getD 9 false = _
    simpa only [List.foldl_append] using H
  rw [original,original] at hg
  exact hw.1 hg

private theorem enum_op (g : Gate) (h : g.op ∈ ({GateOp.and,.or,.not} : Set GateOp)) :
    ∃ i : Fin 3, op i = g.op := by
  rcases h with h|h|h
  · exact ⟨0,h.symm⟩
  · exact ⟨1,h.symm⟩
  · exact ⟨2,h.symm⟩

theorem no_nine (C : Circuit) (hlen : C.gates.length = 5) (hout : C.output = 9)
    (hf : FanInTwo C) (hc : circuitFun 5 C = target)
    (before : ∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 5+j.val)
    (mult : (C.gates.flatMap Gate.inputs : Multiset ℕ) = Multiset.range 9) : False := by
  obtain ⟨gs,out⟩ := C
  change out = 9 at hout
  subst out
  change gs.length = 5 at hlen
  have nod : (ports gs).Nodup :=
    Multiset.coe_nodup.mp (mult ▸ Multiset.nodup_range 9)
  have plen : (ports gs).length = 9 := by
    have e := congrArg Multiset.card mult
    simpa [ports] using e
  have bound (ts : List Gate) (hh : ∀ g ∈ ts, g.inputs.length ≤ 2) : (ports ts).length ≤ 2*ts.length := by
    induction ts with
    | nil => simp [ports]
    | cons g gs ih =>
      have h₁ := hh g (by simp)
      have h₂ := ih (fun t ht => hh t (List.mem_cons_of_mem _ ht))
      simp only [ports,List.flatMap_cons,List.length_append,List.length_cons] at *; omega
  rcases gs with _ | ⟨g,gs⟩
  · simp at hlen
  rcases gs with _ | ⟨h,ts⟩
  · simp at hlen
  have Hg := hf g (by simp)
  have Hh := hf h (by simp)
  have ar := bound ts (fun v hv => (hf v (by simp [hv])).2)
  have sum : g.inputs.length + h.inputs.length + (ports ts).length = 9 := by simpa [ports,Nat.add_assoc] using plen
  have Hg₁ := Hg.2
  have Hh₁ := Hh.2
  have n₃ : ts.length = 3 := by simpa using hlen
  have bg (i) (hi : i ∈ g.inputs) : i < 5 :=
    before ⟨0,by simp⟩ i hi
  have bh (i) (hi : i ∈ h.inputs) : i < 6 :=
    before ⟨1,by simp⟩ i hi
  have hf' (x) : (Circuit.mk (g::h::ts) 9).eval (List.ofFn x) = target x := congrFun hc x
  obtain ⟨i,hi⟩ := enum_op g Hg.1
  obtain ⟨j,hj⟩ := enum_op h Hh.1
  have pair (ls : List ℕ) (hl : ls.length=2) : ∃ a b, ls = [a,b] := by
    rcases ls with _ | ⟨a,ls⟩ <;> simp_all
    rcases ls with _ | ⟨b,ls⟩ <;> simp_all
  by_cases h2 : g.inputs.length = 2
  · obtain ⟨a,b,eq⟩ := pair _ h2
    let A : Fin 5 := ⟨a,bg _ (by simp [eq])⟩
    let B : Fin 5 := ⟨b,bg _ (by simp [eq])⟩
    have eg : short A B i = [g] := by
      cases g; simp only [short,A,B,List.cons.injEq,Gate.mk.injEq, and_true]; exact ⟨hi,eq.symm⟩
    have hn : (ports (short A B i)).Nodup := by
      rw [eg]
      exact (List.nodup_append'.mp (by simpa [ports] using nod)).1
    apply fails (short A B i) (h::ts) _ (short_ok A B i hn)
    · simpa [eg] using nod
    · simp [short,ports]; omega
    · simpa [eg] using hf'
  · have h1 : g.inputs.length = 1 := by omega
    have h2' : h.inputs.length = 2 := by omega
    obtain ⟨a,ea⟩ := List.length_eq_one_iff.mp h1
    obtain ⟨b,c,eb⟩ := pair _ h2'
    let A : Fin 5 := ⟨a,bg _ (by simp [ea])⟩
    let B : Fin 6 := ⟨b,bh _ (by simp [eb])⟩
    let F : Fin 6 := ⟨c,bh _ (by simp [eb])⟩
    have eg : long A B F i j = [g,h] := by
      cases g; cases h
      simp only [long,A,B,F,List.cons.injEq,Gate.mk.injEq,and_true]
      exact ⟨⟨hi,ea.symm⟩,hj,eb.symm⟩
    have hn : (ports (long A B F i j)).Nodup := by
      rw [eg]
      exact (List.nodup_append'.mp (by simpa [ports,List.append_assoc] using nod)).1
    apply fails _ ts _ (long_ok A B F i j hn)
    · simpa [eg] using nod
    · simp [long,ports]; omega
    · simpa [eg] using hf'

end PEqualNP.Outside.Short191
open PEqualNP.Outside PEqualNP.Outside.L_meta_191_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_191 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 5 C → PEqualNP.MetaComplexity.circuitFun 5 C = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∀ j : ℕ, j < 5 → ∃ f ∈ ([fun x => x 0 || x 2, fun x => x 2 || x 4, fun x => x 1 && (x 0 || x 2), fun x => x 3 && (x 2 || x 4), fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))] : List ((Fin 5 → Bool) → Bool)), ∀ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD (5 + j) false = f x) ∧ (∀ f ∈ ([fun x => x 0 || x 2, fun x => x 2 || x 4, fun x => x 1 && (x 0 || x 2), fun x => x 3 && (x 2 || x 4), fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))] : List ((Fin 5 → Bool) → Bool)), ∃ j : ℕ, j < 5 ∧ ∀ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD (5 + j) false = f x) := by
  intro C hm hc
  have hL : C.gates.length = 5 := Size191.size_five C hm hc
  let D := Tidy191.asCircuit 5 C
  have hmD : IsMinimalCircuit 5 D := Tidy191.as_min C hm
  have hD : circuitFun 5 D = Read191.path := (Tidy191.same_fun C hm.1).trans hc
  have hLD : D.gates.length = 5 := (Tidy191.trim_length 5 _).trans hL
  have hgood (i : ℕ) (g : Gate) (he : D.gates[i]? = some g) : Tidy191.good (5+i) g :=
    Tidy191.trim_good 5 C.gates (fun g hg => hm.1 g hg) i g he
  have hh : wireMasks C.gates = wireMasks D.gates :=
    mask_ext191 C D hm.1 hmD.1 (hL.trans hLD.symm) (fun x => (Tidy191.same_wires C hm.1 x).symm)
  apply finish191 C hm hL
  rw [hh]
  apply through_ports D hmD hD hLD hgood
  · have ho := Read191.last_output D hmD (by omega)
    have hn : D.output = 9 := by omega
    apply Short191.no_nine D hLD hn hmD.1 hD
    intro j
    exact (hgood j.val _ (List.getElem?_eq_getElem j.isLt)).2.1
  · intro extra hraw hports hbin hout
    exact expand191 D.gates hLD hbin (fun j g e => (hgood j g e).2.1) ⟨extra,hraw⟩ hports hout
