import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_4837


/- A conjunction of raw bits and previous OR outputs has no OR cost. Substitution preserves the cost of a continuation. Killing an influential bit saves an OR whenever a true row survives. -/

abbrev Row := ℕ → Prop
abbrev Term := Set (Option ℕ)
def read (x : Row) : Option ℕ → Prop
  | none => False
  | some i => x i
def val (u : Term) (x : Row) : Prop := ∀ j ∈ u, read x j
def atom (i : ℕ) : Term := {some i}
def zero : Term := {none}
@[local simp] theorem val_atom (i) (x) : val (atom i) x ↔ x i := by simp [atom,val,read]
@[local simp] theorem val_zero (x) : ¬ val zero x := by simp [zero,val,read]
def push (x : Row) (p : Prop) : Row
  | 0 => p
  | i+1 => x i
def subst (σ : ℕ → Term) (u : Term) : Term :=
  {k | ∃ j ∈ u, k ∈ (j.elim zero σ)}
theorem val_subst (σ : ℕ → Term) (u : Term) (x : Row) :
    val (subst σ u) x ↔ val u (fun i => val (σ i) x) := by
  constructor
  · intro h j hj
    cases j with
    | none => exact h none ⟨none,hj,rfl⟩
    | some j => exact fun k hk => h k ⟨some j,hj,hk⟩
  · intro h k ⟨j,hj,hk⟩
    cases j with
    | none => exact (h none hj).elim
    | some j => exact h (some j) hj k hk
def liftTerm (u : Term) := subst (fun j => atom (j+1)) u
@[local simp] theorem val_liftTerm (u x p) : val (liftTerm u) (push x p) ↔ val u x := by
  simp [liftTerm,val_subst,push]
inductive Cost : ℕ → (Row → Prop) → Prop
  | ret (u : Term) : Cost 0 (val u)
  | join (a b : Term) {r : ℕ} {f : Row → Prop} (tail : Cost r f) :
      Cost (r+1) (fun x => f (push x (val a x ∨ val b x)))
theorem costSub {r f} (h : Cost r f) (σ : ℕ → Term) :
    Cost r (fun x => f (fun i => val (σ i) x)) := by
  induction h generalizing σ with
  | ret u =>
    simpa only [funext (fun x => propext (val_subst σ u x))] using Cost.ret (subst σ u)
  | join a b ht ih =>
    let τ : ℕ → Term := fun j => Nat.casesOn j (atom 0) (fun i => liftTerm (σ i))
    have hh := Cost.join (subst σ a) (subst σ b) (ih τ)
    convert hh using 1
    funext x
    dsimp only
    apply congrArg _
    funext i
    cases i <;> simp [τ,push,val_subst,liftTerm]
def kill (x : Row) (i : ℕ) : Row := Function.update x i False
def Diff (f : Row → Prop) (i : ℕ) := ∃ x, f x ∧ ¬ f (kill x i)
theorem val_kill_of_mem {a : Term} {i} (h : some i ∈ a) (x) : ¬val a (kill x i) := by
  intro hv
  simpa [read,kill] using hv (some i) h
theorem val_kill_of_not_mem {a : Term} {i} (h : some i ∉ a) (x) : val a (kill x i) ↔ val a x := by
  unfold val
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  cases j with
  | none => rfl
  | some j =>
    have hn : j ≠ i := by rintro rfl; exact h hj
    simp [read,kill,Function.update_of_ne hn]
def killSub (i j : ℕ) : Term := if i=j then zero else atom j
theorem val_killSub (i j x) : val (killSub i j) x ↔ kill x i j := by
  by_cases e : i=j
  · subst j; simp [killSub,kill]
  · simp [killSub,e,kill,Function.update_of_ne (Ne.symm e)]
theorem bypass {r f} (ht : Cost r f) (b : Term) :
    Cost r (fun x => f (push x (val b x))) := by
  let σ : ℕ → Term := fun j => Nat.casesOn j b atom
  convert costSub ht σ using 1
  funext x
  congr 1
  funext j
  cases j <;> simp [σ,push]
theorem push_kill (x : Row) (i : ℕ) (p : Prop) :
    kill (push x p) (i+1) = push (kill x i) p := by
  funext j
  cases j with
  | zero => simp [kill,push]
  | succ j =>
    by_cases hj : j=i
    · subst j; simp [kill,push]
    · simp [kill,push,Function.update_of_ne hj,hj]
theorem restrictCost {r f} (ht : Cost r f) (i) :
    Cost r (fun x => f (kill x i)) := by
  simpa only [funext (fun j => propext (val_killSub i j _))] using costSub ht (killSub i)
theorem dropCost {r f} (h : Cost r f) (i : ℕ) (hd : Diff f i)
    (hn : ∃ x, f (kill x i)) : ∃ s < r, Cost s (fun x => f (kill x i)) := by
  classical
  induction h generalizing i with
  | ret u =>
    obtain ⟨x,hx⟩ := hn
    obtain ⟨y,hy,hy'⟩ := hd
    by_cases hi : some i ∈ u
    · exact False.elim (val_kill_of_mem hi x hx)
    · exact False.elim (hy' ((val_kill_of_not_mem hi y).mpr hy))
  | @join a b r f ht ih =>
    by_cases ha : some i ∈ a
    · refine ⟨r,by omega,?_⟩
      simpa only [val_kill_of_mem ha, false_or] using restrictCost (bypass ht b) i
    by_cases hb : some i ∈ b
    · refine ⟨r,by omega,?_⟩
      simpa only [val_kill_of_mem hb, or_false] using restrictCost (bypass ht a) i
    obtain ⟨x,hx,hx'⟩ := hd
    obtain ⟨y,hy⟩ := hn
    let t (z : Row) := val a z ∨ val b z
    have he (z : Row) : t (kill z i) = t z := by
      simp [t,val_kill_of_not_mem ha,val_kill_of_not_mem hb]
    have comm (z : Row) : kill (push z (t z)) (i+1) = push (kill z i) (t (kill z i)) := by
      rw [push_kill,he]
    have hdiff : Diff f (i+1) := ⟨push x (t x),hx,by rwa [comm]⟩
    have hnon : ∃ z, f (kill z (i+1)) := ⟨push y (t y),by rwa [comm]⟩
    obtain ⟨s,hs,hc⟩ := ih (i+1) hdiff hnon
    refine ⟨s+1,by omega,?_⟩
    change Cost (s+1) (fun x => f (push (kill x i) (t (kill x i))))
    simpa only [← comm] using Cost.join a b hc

/- Compile the circuit in gate order. AND gates combine conjunctions and each OR introduces a fresh bit for the remaining gates. -/

open PEqualNP.CircuitLowerBounds
noncomputable section CompilePart
open Classical
def bit (t : Term) (x : Row) : Bool := decide (val t x)
def bits (ws : List Term) (x : Row) := ws.map (bit · x)
@[local simp] theorem bit_zero (x) : bit zero x = false := by simp [bit]
@[local simp] theorem bit_lift (u x p) : bit (liftTerm u) (push x p) = bit u x := by simp [bit]
theorem lookup (ws : List Term) (x : Row) (i) :
    bit (ws.getD i zero) x = (bits ws x).getD i false := by
  simp [bits,List.getD_eq_getElem?_getD,List.getElem?_map,Option.getD_map]
  cases ws[i]? <;> simp
def gateStep (ws : List Bool) (g : Gate) :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
def andTerms (us : List Term) : Term := {k | ∃ u ∈ us, k ∈ u}
theorem bit_and (us : List Term) (x : Row) : bit (andTerms us) x = (bits us x).all id := by
  apply Bool.eq_iff_iff.mpr
  simp [bit,bits,andTerms,val]
  grind
def pick (us : List Term) (j : ℕ) := us.getD j zero
theorem bit_or (us : List Term) (x : Row) (h : us.length ≤ 2) :
    decide (val (pick us 0) x ∨ val (pick us 1) x) = (bits us x).any id := by
  match us with
  | [] => simp [pick,bits]
  | [a] => simp [pick,bits,bit]
  | [a,b] => simp [pick,bits,bit]
  | a::b::c::t => simp at h
def good (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
def nOr (gs : List Gate) := gs.countP (fun g => decide (g.op = .or))
theorem compile (gs : List Gate) (hg : ∀ g ∈ gs, good g) (ws : List Term) (o : ℕ) :
    Cost (nOr gs) (fun x => (gs.foldl gateStep (bits ws x)).getD o false = true) := by
  induction gs generalizing ws with
  | nil =>
    change Cost 0 (fun x => (bits ws x).getD o false = true)
    simpa only [← lookup,bit,decide_eq_true_eq] using Cost.ret (ws.getD o zero)
  | cons g gs ih =>
    have htail := ih (fun g hg' => hg g (List.mem_cons_of_mem _ hg'))
    obtain ⟨hop,hlen⟩ := hg g (by simp)
    let us := g.inputs.map (fun i => ws.getD i zero)
    have hus (x : Row) : bits us x = g.inputs.map (fun i => (bits ws x).getD i false) := by
      simp only [us,bits,List.map_map,Function.comp_def]
      exact List.map_congr_left (fun i _ => lookup ws x i)
    rcases hop with hop|hop
    · have he (x : Row) : gateStep (bits ws x) g = bits (ws ++ [andTerms us]) x := by
        simp only [gateStep,hop,GateOp.eval,bits,List.map_append,List.map_cons,List.map_nil,bit_and]
        exact congrArg (fun l : List Bool => bits ws x ++ [l.all id]) (hus x).symm
      simpa [nOr,hop,he] using htail (ws ++ [andTerms us])
    · let a := pick us 0
      let b := pick us 1
      have hor (x : Row) := bit_or us x (by simpa [us] using hlen)
      have he (x : Row) : gateStep (bits ws x) g =
          bits (ws.map liftTerm ++ [atom 0]) (push x (val a x ∨ val b x)) := by
        simp only [gateStep,hop,GateOp.eval,bits,List.map_append,List.map_map,Function.comp_def,bit_lift,List.map_cons,List.map_nil]
        simp only [bit,val_atom,push,a,b,hor,hus]
        rfl
      simpa [nOr,hop,← he] using Cost.join a b (htail (ws.map liftTerm ++ [atom 0]))
end CompilePart

/- Represent edges by their unordered pairs of raw input indices. Sparsity and the degree sum force degree two on every active vertex once leaves are absent. -/

open Finset
abbrev Edges := Finset (Finset ℕ)
def win (E : Edges) (x : Row) := ∃ e ∈ E, ∀ j ∈ e, x j
def vertices (E : Edges) := E.biUnion id
def degree (E : Edges) (i : ℕ) := (E.filter (i ∈ ·)).card
def del (E : Edges) (i : ℕ) := E.filter (i ∉ ·)
def adj (E : Edges) (i j : ℕ) := ({i,j} : Finset ℕ) ∈ E
structure GraphOK (E : Edges) : Prop where
  two : ∀ e ∈ E, e.card = 2
  sparse : ∀ T : Finset ℕ, (E.filter (· ⊆ T)).card ≤ T.card
  square : ∀ a b c d, a ≠ b → c ≠ d → adj E a c → adj E a d → adj E b c → ¬adj E b d
theorem sub_ok {D E : Edges} (h : GraphOK E) (hs : D ⊆ E) : GraphOK D where
  two e he := h.two e (hs he)
  sparse t := (card_le_card (filter_subset_filter _ hs)).trans (h.sparse t)
  square a b c d hab hcd hac had hbc hbd := h.square a b c d hab hcd (hs hac) (hs had) (hs hbc) (hs hbd)
theorem degree_del (E : Edges) (i : ℕ) : degree E i + (del E i).card = E.card := by
  exact card_filter_add_card_filter_not (i ∈ ·)
theorem win_del (E : Edges) (i : ℕ) (x : Row) : win (del E i) x ↔ win E (kill x i) := by
  simp only [win,del,mem_filter]
  constructor
  · rintro ⟨e,⟨he,hi⟩,hx⟩
    exact ⟨e,he,fun j hj => by simpa [kill,Function.update_of_ne (show j ≠ i by grind)] using hx j hj⟩
  · rintro ⟨e,he,hx⟩
    have hi : i ∉ e := by intro hi; simpa [kill] using hx i hi
    exact ⟨e,⟨he,hi⟩,fun j hj => by simpa [kill,Function.update_of_ne (show j ≠ i by grind)] using hx j hj⟩
theorem win_on (E : Edges) (S : Finset ℕ) : win E (· ∈ S) ↔ ∃ e ∈ E, e ⊆ S := Iff.rfl
theorem pair_win {E : Edges} (h : GraphOK E) (a b : ℕ) :
    win E (· ∈ ({a,b} : Finset ℕ)) ↔ adj E a b := by
  constructor
  · rintro ⟨e,he,hs⟩
    have hcard : ({a,b} : Finset ℕ).card ≤ e.card := by rw [h.two e he]; exact (card_insert_le a {b}).trans (by simp)
    unfold adj; rwa [← eq_of_subset_of_card_le hs hcard]
  · exact fun hh => ⟨_,hh,fun _ hh => hh⟩
theorem no_single {E} (h : GraphOK E) (a : ℕ) : ¬win E (· ∈ ({a} : Finset ℕ)) := by
  rintro ⟨e,he,hs⟩
  have := card_le_card (show e ⊆ {a} from hs)
  simp [h.two e he] at this
theorem adj_ne {E} (h : GraphOK E) {a b : ℕ} (hh : adj E a b) : a ≠ b := by
  rintro rfl
  have := h.two _ hh
  simp at this
theorem adj_of_mem {E} (h : GraphOK E) {e i} (he : e ∈ E) (hi : i ∈ e) :
    ∃ j, e = {i,j} ∧ adj E i j := by
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp (h.two e he)
  simp only [mem_insert,mem_singleton] at hi
  rcases hi with rfl|rfl
  · exact ⟨b,rfl,he⟩
  · exact ⟨a,pair_comm _ _,by simpa [adj,pair_comm i a] using he⟩
theorem win_sens {E} (h : GraphOK E) {i} (hi : 0 < degree E i) : Diff (win E) i := by
  obtain ⟨e,he⟩ := card_pos.mp hi
  obtain ⟨he,hi'⟩ := mem_filter.mp he
  obtain ⟨z,rfl,hz⟩ := adj_of_mem h he hi'
  refine ⟨(· ∈ ({i,z} : Finset ℕ)),(pair_win h _ _).mpr hz,?_⟩
  intro ⟨f,hf,hsub⟩
  apply no_single h z
  refine ⟨f,hf,fun j hj => ?_⟩
  have hh := hsub j hj
  by_cases hji : j=i
  · subst j; simp [kill] at hh
  · simpa [kill,Function.update_of_ne hji,hji] using hh
theorem exists_win {E : Edges} (he : 0 < E.card) : ∃ x, win E x := by
  obtain ⟨e,hh⟩ := card_pos.mp he
  exact ⟨fun _ => True,e,hh,by simp⟩
theorem every_two {E} (h : GraphOK E) (h1 : ∀ i, degree E i ≠ 1) {i} (hi : i ∈ vertices E) :
    degree E i = 2 := by
  classical
  have sub (e) (he : e ∈ E) : e ⊆ vertices E := by intro j hj; exact mem_biUnion.mpr ⟨e,he,hj⟩
  have hs := h.sparse (vertices E)
  rw [filter_true_of_mem sub] at hs
  have hsum : ∑ j ∈ vertices E, degree E j = ∑ e ∈ E, e.card := by
    rw [Finset.sum_congr rfl (fun e (he : e ∈ E) => (show e.card = ((vertices E).filter (· ∈ e)).card by
      congr 1; ext k; simp; exact fun hk => sub _ he hk))] 
    exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun j e => j ∈ e)
  simp only [sum_congr rfl (fun e he => h.two e he),sum_const,nsmul_eq_mul] at hsum
  have hl (j) (hj : j ∈ vertices E) : 2 ≤ degree E j := by
    obtain ⟨e,he,hje⟩ := mem_biUnion.mp hj
    have hp := card_pos.mpr (show (E.filter (j ∈ ·)).Nonempty from ⟨e,mem_filter.mpr ⟨he,hje⟩⟩)
    have := h1 j
    unfold degree at *
    omega
  by_contra hn

  have hh' := Finset.sum_lt_sum (f := fun _ => 2) (g := degree E) (fun j hj => hl j hj)
    (show ∃ j ∈ vertices E, 2 < degree E j from ⟨i,hi,by have := hl i hi; omega⟩)
  simp only [sum_const,nsmul_eq_mul] at hh'
  norm_cast at hsum hh'
  omega

/- Two distinct neighbors and the four-cycle exclusion give rows that remain sensitive after bypassing the first OR. -/

open Finset
theorem term_inter (u : Term) {x y : Row} (hx : val u x) (hy : val u y) :
    val u (fun i => x i ∧ y i) := by
  intro j hj
  cases j with
  | none => exact hx none hj
  | some i => exact ⟨hx _ hj,hy _ hj⟩
theorem ret_bound {E} (h : GraphOK E) (u : Term) (hf : val u = win E) : E.card ≤ 1 := by
  apply card_le_one.mpr
  intro e he d hd
  have accept {s : Finset ℕ} (hs : s ∈ E) : val u (· ∈ s) := by
    rw [hf]; exact ⟨s,hs,fun _ z => z⟩
  have hv := term_inter u (accept he) (accept hd)
  rw [hf] at hv
  obtain ⟨z,hz,hzd⟩ := hv
  have eqe := eq_of_subset_of_card_le (show z ⊆ e from fun j hj => (hzd j hj).1) (by rw [h.two _ he,h.two _ hz])
  have eqd := eq_of_subset_of_card_le (show z ⊆ d from fun j hj => (hzd j hj).2) (by rw [h.two _ hd,h.two _ hz])
  exact eqe.symm.trans eqd
theorem pos_vertices {E i} (h : 0 < degree E i) : i ∈ vertices E := by
  obtain ⟨e,he⟩ := card_pos.mp h
  obtain ⟨he,hi⟩ := mem_filter.mp he
  exact mem_biUnion.mpr ⟨e,he,hi⟩
theorem degree_zero_win {E i} (h : degree E i = 0) (x : Row) : win E (kill x i) ↔ win E x := by
  rw [← win_del]
  have he : del E i = E := by
    apply filter_true_of_mem
    intro e he hi
    have := card_pos.mpr (show (E.filter (i ∈ ·)).Nonempty from ⟨e,mem_filter.mpr ⟨he,hi⟩⟩)
    change 0 < degree E i at this
    omega
  rw [he]
theorem neighbor_other {E} (h : GraphOK E) {i} (hi : degree E i = 2) (b : ℕ) :
    ∃ z, adj E i z ∧ z ≠ b := by
  by_contra! hn
  have hb : (E.filter (i ∈ ·)).card ≤ 1 := by
    apply card_le_one.mpr
    intro e he d hd
    obtain ⟨he,hei⟩ := mem_filter.mp he
    obtain ⟨hd,hdi⟩ := mem_filter.mp hd
    obtain ⟨z,rfl,hz⟩ := adj_of_mem h he hei
    obtain ⟨w,rfl,hw⟩ := adj_of_mem h hd hdi
    rw [hn z hz,hn w hw]
  change degree E i ≤ 1 at hb
  omega
theorem private_neighbor {E} (h : GraphOK E) {i b} (hi : degree E i = 2) (hib : i ≠ b) :
    ∃ z, adj E i z ∧ ¬ adj E b z := by
  by_contra! hn
  obtain ⟨z,hz,_⟩ := neighbor_other h hi i
  obtain ⟨w,hw,hwz⟩ := neighbor_other h hi z
  exact h.square i b w z hib hwz hw hz (hn w hw) (hn z hz)
theorem sensitive_pair {E} (h : GraphOK E) {a b : Term} {f : Row → Prop} {i z}
    (hf : (fun x => f (push x (val a x ∨ val b x))) = win E)
    (hz : adj E i z) (x : Row) (hx : win E x) (hx' : ¬win E (kill x i))
    (h1 : val a x → val b x) (h0 : val a (kill x i) → val b (kill x i)) :
    Diff (fun x => f (push x (val b x))) i := by
  have eqv (y : Row) (hb : val a y → val b y) :
      f (push y (val b y)) = win E y := by
    have hh := congrFun hf y
    simpa only [or_iff_right_of_imp hb] using hh
  exact ⟨x,Eq.mpr (eqv x h1) hx,by simpa only [eqv _ h0] using hx'⟩
theorem pair_rows {E} (h : GraphOK E) {i z} (hz : adj E i z) :
    win E (· ∈ ({i,z} : Finset ℕ)) ∧ ¬ win E (kill (· ∈ ({i,z} : Finset ℕ)) i) := by
  refine ⟨(pair_win h _ _).mpr hz,?_⟩
  intro ⟨f,hf,hsub⟩
  apply no_single h z
  refine ⟨f,hf,fun j hj => ?_⟩
  have hh := hsub j hj
  by_cases hji : j=i
  · subst j; simp [kill] at hh
  · simpa [kill,Function.update_of_ne hji,hji] using hh
theorem multi_sensitive {E} (h : GraphOK E) {a b : Term} {f : Row → Prop} {i j : ℕ}
    (hf : (fun x => f (push x (val a x ∨ val b x))) = win E)
    (hi : degree E i = 2) (hj : some j ∈ a) (hji : j ≠ i) :
    Diff (fun x => f (push x (val b x))) i := by
  obtain ⟨z,hz,hzj⟩ := neighbor_other h hi j
  let x : Row := (· ∈ ({i,z} : Finset ℕ))
  obtain ⟨hp,hn⟩ := pair_rows h hz
  apply sensitive_pair h hf hz x hp hn
  · intro hv; have := hv (some j) hj; simp [read,x,hji,Ne.symm hzj] at this
  · intro hv; have := hv (some j) hj; simp [read,x,kill,Function.update_of_ne hji,hji,Ne.symm hzj] at this
theorem single_sensitive {E} (h : GraphOK E) {i j : ℕ} {f : Row → Prop}
    (hf : (fun x => f (push x (val (atom i) x ∨ val (atom j) x))) = win E)
    (hi : degree E i = 2) (hij : i ≠ j) :
    Diff (fun x => f (push x (val (atom j) x))) i := by
  obtain ⟨z,hz,hjz⟩ := private_neighbor h hi hij
  have hzi := Ne.symm (adj_ne h hz)
  let x : Row := (· ∈ ({i,j,z} : Finset ℕ))
  have hj : x j := by simp [x]
  have hkj : kill x i j := by simpa [kill,Function.update_of_ne (Ne.symm hij)] using hj
  apply sensitive_pair h hf hz x
  · exact ⟨{i,z},hz,by simp [x]⟩
  · intro ⟨e,he,hsub⟩
    apply hjz
    apply (pair_win h j z).mp
    refine ⟨e,he,fun w hw => ?_⟩
    have hh := hsub w hw
    by_cases hwi : w=i
    · subst w; simp [kill] at hh
    · simpa [kill,Function.update_of_ne hwi,x,hwi] using hh
  · simpa using fun (_ : x i) => hj
  · simpa using fun (_ : kill x i i) => hkj

/- Induct on the OR budget. A leaf costs one OR. In the degree-two case bypass the first OR, then kill an input while saving a second OR. -/

open Finset
def Dominates (a b : Term) := ∀ x, val a x → val b x
theorem classify {a b : Term} (ha : ¬ Dominates a b) (hb : ¬ Dominates b a) :
    (∃ i j : ℕ, some i ∈ a ∧ some j ∈ a ∧ i ≠ j) ∨ ∃ i, a = atom i := by
  classical
  have hnone : none ∉ a := fun h => ha (fun x hx => (hx none h).elim)
  have hex : ∃ i : ℕ, some i ∈ a := by
    by_contra! hn
    apply hb
    intro x _ j hj
    cases j with
    | none => exact (hnone hj).elim
    | some j => exact (hn j hj).elim
  obtain ⟨i,hi⟩ := hex
  by_cases hj : ∃ j : ℕ, some j ∈ a ∧ i ≠ j
  · obtain ⟨j,hj,hn⟩ := hj; exact Or.inl ⟨i,j,hi,hj,hn⟩
  · right; refine ⟨i,?_⟩; ext j
    cases j with
    | none => simp [atom,hnone]
    | some j =>
      simp only [atom,Set.mem_singleton_iff,Option.some.injEq]
      exact ⟨fun h => by by_contra hn; exact hj ⟨j,h,Ne.symm hn⟩,fun h => h ▸ hi⟩
theorem lowerBound (r : ℕ) : ∀ E : Edges, GraphOK E → Cost r (win E) → E.card ≤ r+1 := by
  classical
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro E hg hc
    by_contra! hsize
    have step {s D} (hs : s < r) (hd : GraphOK D) (hc : Cost s (win D))
        (hbal : E.card + s ≤ D.card + r) : False := by
      have := ih s hs D hd hc
      omega
    have h1 (i : ℕ) : degree E i ≠ 1 := by
      intro hi
      have hcount := degree_del E i
      have hex := exists_win (E := del E i) (by omega)
      have hn : ∃ x, win E (kill x i) := by simpa only [← win_del] using hex
      obtain ⟨s,hs,hc'⟩ := dropCost hc i (win_sens hg (by omega)) hn
      apply step hs (sub_ok hg (filter_subset _ E)) (D := del E i)
      · simpa only [← win_del] using hc'
      · omega
    generalize hfun : win E = F at hc
    cases hc with
    | ret u =>
      have := ret_bound hg u hfun.symm
      omega
    | @join a b k f ht =>
      have hf := hfun.symm
      have finish {a b : Term} (hf : (fun x => f (push x (val a x ∨ val b x))) = win E)
          (i : ℕ) (hi : some i ∈ a)
          (hsens : degree E i = 2 → Diff (fun x => f (push x (val b x))) i) : False := by
        have he : (fun x => f (push (kill x i) (val b (kill x i)))) = win (del E i) := by
          funext x
          have hh := congrFun hf (kill x i)
          simpa only [val_kill_of_mem hi,false_or,← win_del] using hh
        have hcount := degree_del E i
        have hrest := restrictCost (bypass ht b) i
        by_cases hz : degree E i = 0
        · apply step (s := k) (by omega) (sub_ok hg (filter_subset _ E)) (D := del E i)
          · exact he ▸ hrest
          · omega
        have htwo := every_two hg h1 (pos_vertices (show 0 < degree E i by omega))
        have hpos : 0 < (del E i).card := by omega
        obtain ⟨x,hx⟩ := exists_win hpos
        have hx' := Eq.mpr (congrFun he x) hx
        obtain ⟨s,hs,hc'⟩ := dropCost (bypass ht b) i (hsens htwo) ⟨x,hx'⟩
        apply step (s := s) (by omega) (sub_ok hg (filter_subset _ E)) (D := del E i)
        · exact he ▸ hc'
        · omega
      have swap : (fun x => f (push x (val b x ∨ val a x))) = win E := by simpa only [or_comm] using hf
      have easy {a b : Term} (hf : (fun x => f (push x (val a x ∨ val b x))) = win E)
          (hd : Dominates a b) : False := by
        have eqb : (fun x => f (push x (val b x))) = win E := by
          convert hf using 2 with x
          rw [or_iff_right_of_imp (hd x)]
        apply step (s := k) (by omega) hg (eqb ▸ bypass ht b)
        omega
      by_cases ha : Dominates a b
      · exact easy hf ha
      by_cases hb : Dominates b a
      · exact easy swap hb
      rcases classify ha hb with ⟨i,j,hi,hj,hij⟩|⟨i,rfl⟩
      · exact finish hf i hi (fun hi' => multi_sensitive hg hf hi' hj hij.symm)
      rcases classify hb ha with ⟨j,l,hj,hl,hjl⟩|⟨j,rfl⟩
      · exact finish swap j hj (fun hj' => multi_sensitive hg swap hj' hl hjl.symm)
      have hij : i ≠ j := by rintro rfl; exact ha (fun _ h => h)
      exact finish hf i (by simp [atom]) (fun hi' => single_sensitive hg hf hi' hij)

/- Transfer the finite edge family and four-cycle exclusion from the posted graph. -/

open Finset SimpleGraph
noncomputable section TransferPart
open Classical
def pairMap {n} (e : Sym2 (Fin n)) : Finset ℕ := e.toFinset.image Fin.val
theorem mem_pairMap {n} (e : Sym2 (Fin n)) (j : Fin n) : j.val ∈ pairMap e ↔ j ∈ e := by
  simp [pairMap,Fin.val_injective.eq_iff,Sym2.mem_toFinset]
def emb {n} : Sym2 (Fin n) ↪ Finset ℕ :=
  ⟨pairMap,fun e f he => Sym2.ext (fun j => by rw [←mem_pairMap,←mem_pairMap,he])⟩
def edges {n} (G : SimpleGraph (Fin n)) : Edges := G.edgeFinset.map emb
theorem edge_count {n} (G : SimpleGraph (Fin n)) : (edges G).card = G.edgeSet.ncard := by
  simp [edges,edgeFinset,Set.ncard_eq_toFinset_card']
@[local simp] theorem pairMap_mk {n} (a b : Fin n) : pairMap s(a,b) = {a.val,b.val} := by
  simp [pairMap,Sym2.toFinset_mk_eq]
theorem adj_fin {n} (G : SimpleGraph (Fin n)) (a b : Fin n) :
    adj (edges G) a.val b.val ↔ G.Adj a b := by
  change ({a.val,b.val} : Finset ℕ) ∈ G.edgeFinset.map emb ↔ _
  rw [← pairMap_mk]; change emb s(a,b) ∈ G.edgeFinset.map emb ↔ _
  simp
theorem adj_bounded {n} {G : SimpleGraph (Fin n)} {a b} (h : adj (edges G) a b) : a < n := by
  obtain ⟨e,he,hpair⟩ := mem_map.mp h
  have ha : a ∈ pairMap e := by change a ∈ emb e; rw [hpair]; simp
  obtain ⟨v,_,rfl⟩ := mem_image.mp ha
  exact v.isLt
theorem noSquare {V : Type} {G : SimpleGraph V}
    (h : ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≠ 4)
    {a b c d : V} (hab : a ≠ b) (hcd : c ≠ d) (hac : G.Adj a c)
    (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) : False := by
  let w : G.Walk a a := .cons hac (.cons hbc.symm (.cons hbd (.cons had.symm .nil)))
  apply h a w _ rfl
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  have hne := hac.ne
  have hne' := had.ne
  have hne'' := hbc.ne
  have hne''' := hbd.ne
  simp [w,SimpleGraph.Walk.isPath_def,Ne.symm hab,hab,hcd,Ne.symm hcd,
    hne,hne',hne'',hne''',Ne.symm hne,Ne.symm hne',Ne.symm hne'',Ne.symm hne''']
theorem transfer {n} (G : SimpleGraph (Fin n))
    (hs : ∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card)
    (hc : ∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) : GraphOK (edges G) where
  two e he := by
    obtain ⟨d,hd,rfl⟩ := mem_map.mp he
    change (d.toFinset.image Fin.val).card = 2
    rw [card_image_of_injective _ Fin.val_injective,Sym2.card_toFinset_of_not_isDiag]
    exact G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp hd)
  sparse T := by
    let S := univ.filter (fun i : Fin n => i.val ∈ T)
    have hS : S.card ≤ T.card := by
      rw [← card_image_of_injective S Fin.val_injective]
      apply card_le_card
      intro j hj
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hj
      exact (mem_filter.mp hv).2
    apply le_trans _ hS
    apply le_trans _ (hs S)
    rw [Set.ncard_eq_toFinset_card']
    have heq : ((edges G).filter (· ⊆ T)) =
        ({e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.toFinset.map emb) := by
      ext u
      simp only [edges, mem_filter,mem_map,Set.mem_toFinset,Set.mem_setOf_eq,mem_edgeFinset]
      constructor
      · rintro ⟨⟨e,he,rfl⟩,ht⟩
        exact ⟨e,⟨he,fun v hv => mem_filter.mpr ⟨mem_univ _,ht ((mem_pairMap e v).mpr hv)⟩⟩,rfl⟩
      · rintro ⟨e,⟨he,hv⟩,rfl⟩
        refine ⟨⟨e,he,rfl⟩,?_⟩
        intro j hj
        obtain ⟨v,hv',rfl⟩ := mem_image.mp hj
        exact (mem_filter.mp (hv v (Sym2.mem_toFinset.mp hv'))).2
    rw [heq,card_map]
  square a b c d hab hcd hac had hbc hbd := by
    have boundR {x y} (h : adj (edges G) x y) : y < n :=
      adj_bounded (G := G) (a := y) (b := x) (by simpa [adj,pair_comm y x] using h)
    let A : Fin n := ⟨a,adj_bounded hac⟩
    let B : Fin n := ⟨b,adj_bounded hbc⟩
    let C : Fin n := ⟨c,boundR hac⟩
    let D : Fin n := ⟨d,boundR had⟩
    exact noSquare hc (a := A) (b := B) (c := C) (d := D) (fun eq => hab (congrArg Fin.val eq))
      (fun eq => hcd (congrArg Fin.val eq)) ((adj_fin G A C).mp hac) ((adj_fin G A D).mp had)
      ((adj_fin G B C).mp hbc) ((adj_fin G B D).mp hbd)
end TransferPart

/- Relate accepting rows and the count of OR instructions to the quantities in the statement. -/

open Finset SimpleGraph PEqualNP.CircuitLowerBounds
noncomputable section FinalPart
open Classical
theorem raw_win {n} (G : SimpleGraph (Fin n)) (x : Row) :
    win (edges G) x ↔ ∃ u v : Fin n, G.Adj u v ∧ x u.val ∧ x v.val := by
  constructor
  · rintro ⟨s,he,hs⟩
    obtain ⟨e,he,rfl⟩ := mem_map.mp he
    induction e using Sym2.inductionOn with
    | _ a b =>
      change ∀ j ∈ pairMap s(a,b), x j at hs
      rw [pairMap_mk] at hs
      exact ⟨a,b,by apply (adj_fin G a b).mp; change pairMap s(a,b) ∈ edges G at he; simpa only [adj,pairMap_mk] using he,hs _ (by simp),hs _ (by simp)⟩
  · rintro ⟨a,b,hab,ha,hb⟩
    exact ⟨{a.val,b.val},(adj_fin G a b).mpr hab,by simpa using And.intro ha hb⟩
theorem countBound (gs : List Gate) (k : ℕ) (A : Finset ℕ)
    (h : ∀ j g, gs[j]? = some g → g.op = .or → k+j ∈ A) : nOr gs ≤ A.card := by
  induction gs generalizing k A with
  | nil => simp [nOr]
  | cons g gs ih =>
    by_cases hg : g.op = .or
    · have hk : k ∈ A := by simpa using h 0 g (by simp) hg
      have hh := ih (k+1) (A.erase k) (by
        intro j g' hget hor
        apply mem_erase.mpr
        refine ⟨by omega,?_⟩
        simpa only [Nat.add_assoc,Nat.add_comm 1 j] using h (j+1) g' (by simpa using hget) hor)
      rw [card_erase_of_mem hk] at hh
      have hp := card_pos.mpr (show A.Nonempty from ⟨k,hk⟩)
      have hs : nOr (g :: gs) = nOr gs + 1 := by simp [nOr,hg]
      rw [hs]
      omega
    · have hh := ih (k+1) A (by
        intro j g' hget hor
        simpa only [Nat.add_assoc,Nat.add_comm 1 j] using h (j+1) g' (by simpa using hget) hor)
      simpa [nOr,hg] using hh
end FinalPart

end PEqualNP.Outside.L_meta_4837

open PEqualNP.Outside.L_meta_4837

theorem PEqualNP.Outside.L_meta_4837 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → G.edgeSet.ncard ≤ A.card + 1 := by
  classical
  intro n G C A hs hc hm he hA
  let ws := List.ofFn (fun i : Fin n => atom i.val)
  have hbits (x : Row) : bits ws x = List.ofFn (fun i : Fin n => decide (x i.val)) := by
    simp [ws,bits,List.map_ofFn,Function.comp_def,bit,val_atom]
  have hgood (g) (hg : g ∈ C.gates) : good g := by
    simpa [good] using hm g hg
  have hh := compile C.gates hgood ws C.output
  have hfun : (fun x => (C.gates.foldl gateStep (bits ws x)).getD C.output false = true) = win (edges G) := by
    funext x
    rw [hbits]
    change (C.eval (List.ofFn (fun i : Fin n => decide (x i.val))) = true) = _
    apply propext
    rw [he,raw_win]
    simp
  rw [hfun] at hh
  have hlo := lowerBound _ _ (transfer G hs hc) hh
  have hcount := countBound C.gates 0 A (by simpa using hA)
  rw [edge_count] at hlo
  omega
