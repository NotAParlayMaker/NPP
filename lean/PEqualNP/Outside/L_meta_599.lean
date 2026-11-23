import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta599
abbrev Term (V : Type) := Option (List V)

def val (x : V → Bool) : Term V → Bool
  | none => false
  | some vs => vs.all x

def atom (v : V) : Term V := some [v]

def meet : Term V → Term V → Term V
  | some a, some b => some (a ++ b)
  | _, _ => none

def substT (f : V → Term W) : Term V → Term W
  | none => none
  | some vs => vs.foldr (fun v t => meet (f v) t) (some [])

@[simp] theorem val_atom (x : V → Bool) (v : V) : val x (atom v) = x v := by simp [atom, val]
@[simp] theorem val_meet (x : V → Bool) (a b : Term V) :
    val x (meet a b) = (val x a && val x b) := by cases a <;> cases b <;> simp [meet,val]
@[simp] theorem val_sub (f : V → Term W) (x : W → Bool) (a : Term V) :
    val x (substT f a) = val (fun v => val x (f v)) a := by
  cases a with
  | none => rfl
  | some vs =>
    change val x (vs.foldr _ _) = vs.all _
    induction vs with
    | nil => rfl
    | cons v vs ih => simp only [List.foldr_cons, val_meet, ih, List.all_cons]

inductive Plan : Type → Type 1
  | ret {V} : Term V → Plan V
  | gate {V} : Term V → Term V → Plan (Option V) → Plan V

def eval : Plan V → (V → Bool) → Bool
  | .ret a, x => val x a
  | .gate a b p, x => eval p (fun | none => val x a || val x b | some v => x v)

def cost : Plan V → Nat
  | .ret _ => 0
  | .gate _ _ p => cost p + 1

def tagged (v : V) (t : Term V) : Prop := ∃ vs, t = some vs ∧ v ∈ vs

noncomputable def hits (v : V) (p : Plan V) : Nat := by
  classical
  exact match p with
    | .ret _ => 0
    | .gate a b q => (if tagged v a ∨ tagged v b then 1 else 0) + hits (some v) q

theorem deadTerm (f : V → Term W) (v : V) (hv : f v = none) (t : Term V)
    (h : tagged v t) : substT f t = none := by
  obtain ⟨vs, rfl, hv'⟩ := h
  change vs.foldr _ _ = _
  induction vs with
  | nil => simp at hv'
  | cons w ws ih =>
    rcases List.mem_cons.mp hv' with e | e
    · subst w; simp [hv, meet]
    · simp only [List.foldr_cons, ih e]; cases f w <;> rfl

def liftF (f : V → Term W) : Option V → Term (Option W)
  | none => atom none
  | some v => substT (fun w => atom (some w)) (f v)

def smartSub (p : Plan V) (f : V → Term W) : Plan W :=
  match p with
  | .ret a => .ret (substT f a)
  | .gate a b q =>
    match substT f a, substT f b with
    | none, t | t, none => smartSub q (fun | none => t | some v => f v)
    | some as', some bs' => .gate (some as') (some bs') (smartSub q (liftF f))

theorem sub_eval (p : Plan V) (f : V → Term W) (x : W → Bool) :
    eval (smartSub p f) x = eval p (fun v => val x (f v)) := by
  induction p generalizing W with
  | ret a => exact val_sub ..
  | gate a b q ih =>
    simp only [smartSub, eval]
    generalize ha : substT f a = a'
    generalize hb : substT f b = b'
    have ea := val_sub f x a
    have eb := val_sub f x b
    rw [ha] at ea
    rw [hb] at eb
    cases a' <;> cases b' <;> simp only [eval, ih] <;> congr 1 <;> funext z <;>
      cases z <;> simp only [liftF, val_sub, val_atom, ← ea, ← eb] <;> first | rfl | change _ = (false || _); rfl | change _ = (_ || false); simp

theorem sub_cost (p : Plan V) (f : V → Term W) : cost (smartSub p f) ≤ cost p := by
  induction p generalizing W with
  | ret => exact Nat.le_refl _
  | gate a b q ih =>
    simp only [smartSub, cost]
    cases substT f a <;> cases substT f b <;> simp only [cost]
    all_goals first | exact Nat.le_succ_of_le (ih _) | exact Nat.succ_le_succ (ih _)

theorem sub_savings (p : Plan V) (f : V → Term W) (v : V) (hv : f v = none) :
    cost (smartSub p f) + hits v p ≤ cost p := by
  classical
  induction p generalizing W with
  | ret => simp [smartSub, cost, hits]
  | gate a b q ih =>
    simp only [smartSub, cost, hits]
    generalize ha : substT f a = a'
    generalize hb : substT f b = b'
    have d : tagged v a ∨ tagged v b → a' = none ∨ b' = none := by
      rintro (h | h)
      · exact Or.inl (ha.symm.trans (deadTerm f v hv a h))
      · exact Or.inr (hb.symm.trans (deadTerm f v hv b h))
    cases a' <;> cases b' <;> simp only [cost]
    case none.none =>
      have h := ih (fun | none => (none : Term W) | some w => f w) (some v) hv
      split <;> omega
    case none.some ys =>
      have h := ih (fun | none => (some ys : Term W) | some w => f w) (some v) hv
      split <;> omega
    case some.none xs =>
      have h := ih (fun | none => (some xs : Term W) | some w => f w) (some v) hv
      split <;> omega
    case some.some xs ys =>
      have h := ih (liftF f) (some v) (by simp [liftF, hv, substT])
      split <;> simp_all <;> omega
end PEqualNP.Outside.Meta599

namespace PEqualNP.Outside.Meta599

def outTag (v : V) (p : Plan V) : Prop := match p with
  | .ret t => tagged v t
  | .gate _ _ q => outTag (some v) q

theorem tagged_true (t : Term V) (x : V → Bool) (ht : val x t = true) (hv : tagged v t) :
    x v = true := by
  obtain ⟨vs,rfl,hv⟩ := hv
  exact List.all_eq_true.mp ht v hv

theorem outTag_true (p : Plan V) (v : V) (x : V → Bool) (he : eval p x = true)
    (hv : outTag v p) : x v = true := by
  induction p with
  | ret t => exact tagged_true t x he hv
  | gate a b q ih => exact ih (some v) _ he hv

theorem val_agree (t : Term V) (x y : V → Bool) (h : ∀ v, tagged v t → x v = y v) :
    val x t = val y t := by
  cases t with
  | none => rfl
  | some vs =>
    change vs.all x = vs.all y
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro hh v hv
    · rw [← h v ⟨vs,rfl,hv⟩]; exact hh v hv
    · rw [h v ⟨vs,rfl,hv⟩]; exact hh v hv

theorem eval_agree (p : Plan V) (x y : V → Bool)
    (h : ∀ v, hits v p ≠ 0 ∨ outTag v p → x v = y v) : eval p x = eval p y := by
  classical
  induction p with
  | ret t => exact val_agree t x y (fun v hv => h v (Or.inr hv))
  | gate a b q ih =>
    apply ih
    intro z hz
    cases z with
    | none =>
      have get (v : _) (hv : tagged v a ∨ tagged v b) : x v = y v := by
        apply h v (Or.inl ?_)
        simp [hits, hv]
      change (val x a || val x b) = (val y a || val y b)
      rw [val_agree a x y (fun v hv => get v (Or.inl hv)),
          val_agree b x y (fun v hv => get v (Or.inr hv))]
    | some v =>
      apply h v
      rcases hz with hz | hz
      · left; simp only [hits]; split <;> omega
      · exact Or.inr hz

end PEqualNP.Outside.Meta599

namespace PEqualNP.Outside.Meta599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def liftT (t : Term V) : Term (Option V) := substT (fun v => atom (some v)) t

def both (w : List (Term V)) (ins : List ℕ) : Term V :=
  ins.foldr (fun i t => meet (w.getD i none) t) (some [])

def compile (gs : List Gate) (out : ℕ) (ws : List (Term V)) : Plan V :=
  match gs with
  | [] => .ret (ws.getD out none)
  | g :: gs =>
    match g.op with
    | .or =>
      .gate (ws.getD (g.inputs.getD 0 ws.length) none)
        (ws.getD (g.inputs.getD 1 ws.length) none)
        (compile gs out (ws.map liftT ++ [atom none]))
    | _ => compile gs out (ws ++ [both ws g.inputs])

def ok (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def run (gs : List Gate) (ws : List Bool) (out : ℕ) :=
  (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws).getD out false

theorem val_at (x : V → Bool) (ws : List (Term V)) (i : ℕ) :
    val x (ws.getD i none) = (ws.map (val x)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> rfl

theorem val_both (x : V → Bool) (ws : List (Term V)) (ins : List ℕ) :
    val x (both ws ins) = GateOp.and.eval (ins.map fun i => (ws.map (val x)).getD i false) := by
  induction ins with
  | nil => rfl
  | cons i is ih =>
    change val x (meet _ (both ws is)) = (_ && _)
    rw [val_meet, val_at, ih]; rfl

theorem val_or (x : V → Bool) (w : List (Term V)) (ins : List ℕ) (h : ins.length ≤ 2) :
    (val x (w.getD (ins.getD 0 w.length) none) || val x (w.getD (ins.getD 1 w.length) none)) =
    GateOp.or.eval (ins.map fun i => (w.map (val x)).getD i false) := by
  have o : w.getD w.length none = none := List.getD_eq_default _ _ (by omega)
  cases ins with
  | nil => simp [GateOp.eval, o, val]
  | cons a ts => cases ts with
    | nil =>
      change (val x (w.getD a none) || val x (w.getD w.length none)) = (_ || false)
      rw [o,val_at]; rfl
    | cons b ts => cases ts with
      | nil =>
        change (_ || _) = (_ || (_ || false))
        simp only [Bool.or_false, ← val_at]; rfl
      | cons c cs => simp at h

theorem compile_ok (gs : List Gate) (out : ℕ) (ws : List (Term V)) (x : V → Bool)
    (h : ∀ g ∈ gs, ok g) : eval (compile gs out ws) x = run gs (ws.map (val x)) out := by
  induction gs generalizing V with
  | nil => exact val_at ..
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := h g (by simp)
    have htail : ∀ g ∈ gs, ok g := fun u hu => h u (by simp [hu])
    rcases hop with hop | hop
    · simp only [compile, hop, ih _ _ htail, List.map_append, List.map_cons, List.map_nil, val_both]
      simp [run, hop]
    · simp only [compile, hop, eval, ih _ _ htail, List.map_append, List.map_cons, List.map_nil,
        List.map_map, Function.comp_def, liftT, val_sub, val_atom, val_or x ws _ hlen]
      simp [run, hop]

def nOr : List Gate → ℕ
  | [] => 0
  | g :: gs => match g.op with
    | .or => nOr gs + 1
    | _ => nOr gs

theorem compile_cost (gs : List Gate) (out : ℕ) (ws : List (Term V)) :
    cost (compile gs out ws) = nOr gs := by
  induction gs generalizing V with
  | nil => rfl
  | cons g gs ih => cases g with | mk op ins => cases op <;> simp [compile,nOr,cost,ih]

end PEqualNP.Outside.Meta599

namespace PEqualNP.Outside.Meta599
variable {V : Type} [Fintype V]

noncomputable def edges (G : SimpleGraph V) := G.edgeSet.ncard
noncomputable def deg (G : SimpleGraph V) (v : V) := (G.neighborSet v).ncard
def sparse (G : SimpleGraph V) := ∀ S : Finset V,
  {e : Sym2 V | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card
def squareFree (G : SimpleGraph V) := ∀ a b c d : V, a ≠ b → c ≠ d →
  G.Adj a c → G.Adj a d → G.Adj b c → G.Adj b d → False
def active (G : SimpleGraph V) (x : V → Bool) := ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
def represents (p : Plan V) (G : SimpleGraph V) := ∀ x, eval p x = true ↔ active G x

theorem sq_of_walk (G : SimpleGraph V)
    (h : ∀ v (c : G.Walk v v), c.IsCycle → c.length ≠ 4) : squareFree G := by
  intro a b c d hab hcd hac had hbc hbd
  let p : G.Walk a a := .cons hac (.cons hbc.symm (.cons hbd (.cons had.symm .nil)))
  apply h a p _ rfl
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  have hca := hac.ne.symm
  have hda := had.ne.symm
  have hcb := hbc.ne.symm
  have hdb := hbd.ne.symm
  simp [p, SimpleGraph.Walk.isPath_def, *, ne_comm] <;> exact hbd.ne

theorem smaller_sparse (G H : SimpleGraph V) (le : H ≤ G) (h : sparse G) : sparse H := by
  intro S
  exact (Set.ncard_le_ncard (s := {e : Sym2 V | e ∈ H.edgeSet ∧ ∀ v ∈ e, v ∈ S})
    (t := {e : Sym2 V | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S})
    (fun e he => ⟨SimpleGraph.edgeSet_mono le he.1, he.2⟩)).trans (h S)

theorem smaller_sq (G H : SimpleGraph V) (le : H ≤ G) (h : squareFree G) : squareFree H :=
  fun a b c d h1 h2 ac ad bc bd => h a b c d h1 h2 (le ac) (le ad) (le bc) (le bd)

theorem edges_card (G : SimpleGraph V) [Fintype G.edgeSet] :
    edges G = G.edgeFinset.card := by
  rw [edges, Set.ncard_eq_toFinset_card']; rfl

theorem deg_card (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    deg G v = G.degree v := by
  rw [deg, Set.ncard_eq_toFinset_card']; rfl

theorem deletion (G : SimpleGraph V) (v : V) :
    edges (G.deleteIncidenceSet v) + deg G v = edges G := by
  classical
  have h : G.incidenceSet v ⊆ G.edgeSet := G.incidenceSet_subset v
  have eq : (G.incidenceSet v).ncard = deg G v := by
    rw [Set.ncard_eq_toFinset_card', deg_card, ← G.card_incidenceFinset_eq_degree v]; rfl
  rw [edges, G.edgeSet_deleteIncidenceSet, ← eq]
  exact Set.ncard_sdiff_add_ncard_of_subset h

theorem regular (G : SimpleGraph V) (hs : sparse G) (hl : ∀ v, deg G v ≠ 1) :
    ∀ v, deg G v ≤ 2 := by
  classical
  let S := G.support.toFinset
  have hS : edges G ≤ S.card := by
    have eq : {e : Sym2 V | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} = G.edgeSet := by
      ext e
      constructor
      · exact fun h => h.1
      · intro he; refine ⟨he, fun v hv => ?_⟩
        apply Set.mem_toFinset.mpr
        induction e using Sym2.inductionOn with
        | _ a b =>
          have ab : G.Adj a b := he
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact ab.mem_support_left
          · exact ab.mem_support_right
    simpa [eq, edges] using hs S
  have hd : ∀ v ∈ S, 2 ≤ G.degree v := by
    intro v hv
    have hp := (G.degree_pos_iff_mem_support v).2 (Set.mem_toFinset.mp hv)
    have := hl v; rw [deg_card] at this; omega
  have hsum : ∑ v ∈ S, G.degree v = 2 * edges G := by
    rw [Finset.sum_subset (Finset.subset_univ S) (f := fun z => G.degree z)]
    · rw [G.sum_degrees_eq_twice_card_edges, edges_card]
    · intro v _ hv; exact (G.degree_eq_zero_iff_notMem_support v).2 (by simpa [S] using hv)
  intro v
  rw [deg_card]
  by_contra! h
  have hv : v ∈ S := Set.mem_toFinset.mpr ((G.degree_pos_iff_mem_support v).mp (by omega))
  have hlt := Finset.sum_lt_sum hd ⟨v,hv,h⟩
  simp only [Finset.sum_const, smul_eq_mul, hsum] at hlt
  omega
end PEqualNP.Outside.Meta599

namespace PEqualNP.Outside.Meta599
variable {V : Type} [Fintype V] [DecidableEq V]

def pair (a b : V) (z : V) := decide (z = a ∨ z = b)
@[simp] theorem pair_on (a b z : V) : pair a b z = true ↔ z = a ∨ z = b := by simp [pair]

theorem test_pair (G : SimpleGraph V) (a b : V) : active G (pair a b) ↔ G.Adj a b := by
  constructor
  · rintro ⟨u,v,adj,hu,hv⟩
    rcases (pair_on ..).mp hu with rfl | rfl <;> rcases (pair_on ..).mp hv with rfl | rfl
    all_goals first | exact adj | exact adj.symm | exact (adj.ne rfl).elim
  · exact fun h => ⟨a,b,h,by simp,by simp⟩

def pin (v z : V) : Term V := if z = v then none else atom z

theorem pin_rep (p : Plan V) (G : SimpleGraph V) (h : represents p G) (v : V) :
    represents (smartSub p (pin v)) (G.deleteIncidenceSet v) := by
  intro x
  rw [sub_eval, h]
  simp only [active, SimpleGraph.deleteIncidenceSet_adj]
  have hp (u : V) : val x (pin v u) = true ↔ u ≠ v ∧ x u = true := by
    by_cases e : u = v <;> simp [pin,e,val,atom]
  simp only [hp]
  grind

theorem edge_of_pos (G : SimpleGraph V) (h : 0 < edges G) : ∃ a b, G.Adj a b := by
  classical
  obtain ⟨e,he⟩ := Set.nonempty_of_ncard_ne_zero (s := G.edgeSet) (Nat.ne_of_gt h)
  induction e using Sym2.inductionOn with
  | _ a b => exact ⟨a,b,he⟩

theorem out_free (p : Plan V) (G : SimpleGraph V) (h : represents p G) (v : V)
    (other : ∃ a b, G.Adj a b ∧ a ≠ v ∧ b ≠ v) : ¬ outTag v p := by
  rintro ht
  obtain ⟨a,b,ab,ha,hb⟩ := other
  have t := outTag_true p v (pair a b) ((h _).2 ((test_pair ..).2 ab)) ht
  exact ((pair_on ..).mp t).elim (fun e => ha e.symm) (fun e => hb e.symm)

theorem essential (p : Plan V) (G : SimpleGraph V) (h : represents p G) {v w : V}
    (vw : G.Adj v w) : hits v p ≠ 0 ∨ outTag v p := by
  classical
  by_contra H
  have equal := eval_agree p (pair v w) (pair w w) (by
    intro z hz
    have : z ≠ v := fun e => H (e ▸ hz)
    simp [pair,this])
  have yes := (h _).2 ((test_pair ..).2 vw)
  have no := (test_pair ..).1 ((h _).1 (equal ▸ yes))
  exact no.ne rfl

theorem two_nbrs (G : SimpleGraph V) (v : V) (h : 2 ≤ deg G v) :
    ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  classical
  rw [deg_card, ← G.card_neighborFinset_eq_degree] at h
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp h
  exact ⟨a,b,ne,(G.mem_neighborFinset v a).mp ha,(G.mem_neighborFinset v b).mp hb⟩

theorem cycle_other (G : SimpleGraph V) (d : ∀ v, deg G v ≠ 1) {v w : V} (vw : G.Adj v w) :
    ∃ a b, G.Adj a b ∧ a ≠ v ∧ b ≠ v := by
  classical
  have hp := (G.degree_pos_iff_exists_adj w).2 ⟨v,vw.symm⟩
  rw [← deg_card] at hp
  obtain ⟨a,b,ab,wa,wb⟩ := two_nbrs G w (by have := d w; omega)
  by_cases av : a = v
  · exact ⟨w,b,wb,vw.ne.symm,by grind⟩
  · exact ⟨w,a,wa,vw.ne.symm,av⟩

end PEqualNP.Outside.Meta599

namespace PEqualNP.Outside.Meta599
variable {V : Type} [Fintype V] [DecidableEq V]

def hidden (q : Plan (Option V)) (v : V) := hits (some v) q = 0 ∧ ¬ outTag (some v) q

theorem same_output (a b : Term V) (q : Plan (Option V)) (x y : V → Bool)
    (gateEq : (val x a || val x b) = (val y a || val y b))
    (off : ∀ v, x v ≠ y v → hidden q v) :
    eval (.gate a b q) x = eval (.gate a b q) y := by
  apply eval_agree q
  intro z hz
  cases z with
  | none => exact gateEq
  | some v =>
    by_contra e
    obtain ⟨h0, h1⟩ := off v e
    exact hz.elim (fun h => h h0) h1

theorem exclusive_single (G : SimpleGraph V) (s t : List V) (v : V)
    (vs : v ∈ s) (vt : v ∉ t) (d : 2 ≤ deg G v)
    (factor : ∀ x y : V → Bool, (∀ z, z ≠ v → x z = y z) →
        (x |> fun x => s.all x || t.all x) = (s.all y || t.all y) → (active G x ↔ active G y)) :
    ∀ z ∈ s, z = v := by
  intro z zs
  by_contra zv
  obtain ⟨a,b,ab,va,vb⟩ := two_nbrs G v d
  obtain ⟨w, vw, zw⟩ : ∃ w, G.Adj v w ∧ z ≠ w := by
    by_cases h : z = a
    · exact ⟨b,vb,h ▸ ab⟩
    · exact ⟨a,va,h⟩
  have off (u : V) (uv : u ≠ v) : pair v w u = pair w w u := by simp [pair,uv]
  have s0 : s.all (pair v w) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact ((pair_on ..).mp (List.all_eq_true.mp ht z zs)).elim zv zw
  have s1 : s.all (pair w w) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact ((pair_on ..).mp (List.all_eq_true.mp ht z zs)).elim zw zw
  have te := val_agree (some t) (pair v w) (pair w w) (by
    intro u hu
    obtain ⟨us,e,mem⟩ := hu
    cases e
    exact off u (fun eq => vt (eq ▸ mem)))
  change t.all _ = t.all _ at te
  have f := factor _ _ off (by simp [s0,s1,te])
  exact ((test_pair G w w).mp (f.mp ((test_pair ..).mpr vw))).ne rfl

theorem avoid_bridge (G : SimpleGraph V) (sq : squareFree G) (s t : List V)
    (q : Plan (Option V)) (rep : represents (.gate (some s) (some t) q) G)
    (allH : ∀ v, v ∈ s ∨ v ∈ t → hidden q v)
    (allD : ∀ v, v ∈ s ∨ v ∈ t → 2 ≤ deg G v)
    (u v : V) (us : u ∈ s) (ut : u ∉ t) (vt : v ∈ t) (vs : v ∉ s) : False := by
  have transfer (x y : V → Bool)
      (hgate : (s.all x || t.all x) = (s.all y || t.all y))
      (hh : ∀ z, x z ≠ y z → hidden q z) : active G x ↔ active G y := by
    rw [← rep x, ← rep y, same_output (some s) (some t) q x y hgate hh]
  have ss := exclusive_single G s t u us ut (allD _ (Or.inl us)) (by
    intro x y off e
    apply transfer x y e
    intro z diff
    have : z = u := Classical.byContradiction fun ne => diff (off z ne)
    exact this ▸ allH u (Or.inl us))
  have tt := exclusive_single G t s v vt vs (allD _ (Or.inr vt)) (by
    intro x y off e
    apply transfer x y (by simpa only [Bool.or_comm] using e)
    intro z diff
    have : z = v := Classical.byContradiction fun ne => diff (off z ne)
    exact this ▸ allH v (Or.inr vt))
  have twin (w : V) (uw : G.Adj u w) : G.Adj v w := by
    have left : s.all (pair u w) = true := List.all_eq_true.mpr fun z hz => by rw [ss z hz]; simp
    have right : t.all (pair v w) = true := List.all_eq_true.mpr fun z hz => by rw [tt z hz]; simp
    have iff := transfer (pair u w) (pair v w) (by simp [left,right]) (by
      intro z diff
      by_cases zu : z = u
      · subst z; exact allH _ (Or.inl us)
      by_cases zv : z = v
      · subst z; exact allH _ (Or.inr vt)
      exact (diff (by simp [pair,zu,zv])).elim)
    exact (test_pair ..).mp (iff.mp ((test_pair ..).mpr uw))
  obtain ⟨a,b,ne,ua,ub⟩ := two_nbrs G u (allD _ (Or.inl us))
  exact sq u v a b (fun e => vs (e ▸ us)) ne ua ub (twin a ua) (twin b ub)

end PEqualNP.Outside.Meta599

namespace PEqualNP.Outside.Meta599
variable {V : Type} [Fintype V] [DecidableEq V]

theorem skip_first (a b t : Term V) (q : Plan (Option V))
    (same : ∀ x, (val x a || val x b) = val x t) :
    ∃ p : Plan V, cost p ≤ cost q ∧ ∀ x, eval p x = eval (.gate a b q) x := by
  let f : Option V → Term V := fun | none => t | some v => atom v
  refine ⟨smartSub q f, sub_cost .., ?_⟩
  intro x; rw [sub_eval]
  apply congrArg (eval q); funext z; cases z with
  | none => exact (same x).symm
  | some v => exact val_atom ..

theorem absorb (s t : List V) (sub : ∀ v ∈ s, v ∈ t) (x : V → Bool) :
    (s.all x || t.all x) = s.all x := by
  have imp : t.all x = true → s.all x = true :=
    fun h => List.all_eq_true.mpr fun v hv => List.all_eq_true.mp h v (sub v hv)
  cases ha : s.all x <;> cases hb : t.all x <;> simp_all

theorem bound_aux (k : ℕ) : ∀ (G : SimpleGraph V) (p : Plan V),
    edges G + cost p ≤ k → sparse G → squareFree G → represents p G → edges G ≤ cost p + 1 := by
  classical
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro G p size hs sq rep
    by_contra! bad
    have minimal (H : SimpleGraph V) (q : Plan V)
        (lt : edges H + cost q < edges G + cost p)
        (hs' : sparse H) (sq' : squareFree H) (rep' : represents q H) :
        edges H ≤ cost q + 1 := ih _ (by omega) H q (Nat.le_refl _) hs' sq' rep'
    have accounting (v : V) (drop : 0 < deg G v ∨ 0 < hits v p) : hits v p < deg G v := by
      have saved := sub_savings p (pin v) v (by simp [pin])
      have cut := deletion G v
      have le := G.deleteIncidenceSet_le v
      have bound := minimal _ _ (by rcases drop with d | d <;> omega)
        (smaller_sparse _ _ le hs) (smaller_sq _ _ le sq) (pin_rep p G rep v)
      omega
    have noLeaf (v : V) : deg G v ≠ 1 := by
      intro one
      have acct := accounting v (Or.inl (by omega))
      have cut := deletion G v
      obtain ⟨u,w,uw⟩ := edge_of_pos (G.deleteIncidenceSet v) (by omega)
      obtain ⟨uw,uv,wv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp uw
      have free := out_free p G rep v ⟨u,w,uw,uv,wv⟩
      have pos : 0 < G.degree v := by rw [← deg_card, one]; decide
      obtain ⟨z,vz⟩ := (G.degree_pos_iff_exists_adj v).mp pos
      have use := (essential p G rep vz).resolve_right free
      omega
    have small := regular G hs noLeaf
    have uses (v : V) (hit : 0 < hits v p) : deg G v = 2 ∧ hits v p = 1 ∧ ¬ outTag v p := by
      have acct := accounting v (Or.inr hit)
      have dv := small v
      have pos : 0 < G.degree v := by rw [← deg_card]; omega
      obtain ⟨z,vz⟩ := (G.degree_pos_iff_exists_adj v).mp pos
      exact ⟨by omega,by omega,out_free p G rep v (cycle_other G noLeaf vz)⟩
    cases p with
    | ret t =>
      obtain ⟨v,w,vw⟩ := edge_of_pos G (by omega)
      have free := out_free (.ret t) G rep v (cycle_other G noLeaf vw)
      exact ((essential _ _ rep vw).resolve_right free) (by rfl)
    | gate a b q =>
      have irr (t : Term V) (eq : ∀ x, (val x a || val x b) = val x t) : False := by
        obtain ⟨r,hr,he⟩ := skip_first a b t q eq
        have hcost : cost (.gate a b q) = cost q + 1 := rfl
        have br := minimal G r (by omega) hs sq (fun x => (he x) ▸ rep x)
        omega
      cases a with
      | none => exact irr b (fun x => by rfl)
      | some s =>
        cases b with
        | none => exact irr (some s) (fun x => by change (_ || false) = _; simp)
        | some t =>
          by_cases sub : ∀ v ∈ s, v ∈ t
          · exact irr (some s) (absorb s t sub)
          by_cases sub' : ∀ v ∈ t, v ∈ s
          · exact irr (some t) (fun x => (Bool.or_comm ..).trans (absorb t s sub' x))
          push_neg at sub sub'
          obtain ⟨u,us,ut⟩ := sub
          obtain ⟨v,vt,vs⟩ := sub'
          have facts (z : V) (hz : z ∈ s ∨ z ∈ t) :
              2 ≤ deg G z ∧ hidden q z := by
            have tag : tagged z (some s) ∨ tagged z (some t) :=
              hz.elim (fun h => Or.inl ⟨s,rfl,h⟩) (fun h => Or.inr ⟨t,rfl,h⟩)
            have hit : hits z (.gate (some s) (some t) q) = 1 + hits (some z) q := by simp [hits,tag]
            obtain ⟨degree,one,out⟩ := uses z (by omega)
            exact ⟨by omega,by unfold hidden; exact ⟨by omega,out⟩⟩
          exact avoid_bridge G sq s t q rep (fun z h => (facts z h).2) (fun z h => (facts z h).1)
            u v us ut vt vs

end PEqualNP.Outside.Meta599

namespace PEqualNP.Outside.Meta599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def succEmb : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩

def positions : List Gate → Finset ℕ
  | [] => ∅
  | g :: gs =>
    match g.op with
    | .or => insert 0 ((positions gs).map succEmb)
    | _ => (positions gs).map succEmb

theorem pos_count (gs : List Gate) : (positions gs).card = nOr gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have zero : 0 ∉ (positions gs).map succEmb := by simp [succEmb]
    cases g with | mk op ins => cases op <;> simp [positions,nOr,zero,ih]

theorem pos_valid (gs : List Gate) (j : ℕ) (h : j ∈ positions gs) :
    ∃ g, gs[j]? = some g ∧ g.op = GateOp.or := by
  induction gs generalizing j with
  | nil => simp [positions] at h
  | cons g gs ih =>
    have fromTail (h : j ∈ (positions gs).map succEmb) : ∃ x, (g::gs)[j]? = some x ∧ x.op = .or := by
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp h
      exact ih k hk
    cases g with
    | mk op ins =>
      cases op <;> simp only [positions] at h
      all_goals first
        | exact fromTail h
        | rcases Finset.mem_insert.mp h with rfl | ht
          · exact ⟨_,rfl,rfl⟩
          · exact fromTail ht

theorem fromCircuit (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ)
    (hs : sparse G) (sq : squareFree G) (hm : Monotone2 C)
    (rep : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ active G x)
    (incl : ∀ j g, C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) : edges G ≤ A.card + 1 := by
  let ws : List (Term (Fin n)) := List.ofFn atom
  let p := compile C.gates C.output ws
  have good (g : Gate) (mem : g ∈ C.gates) : ok g := by
    obtain ⟨op,h⟩ := hm g mem
    exact ⟨by simpa using op,h⟩
  have representsP : represents p G := by
    intro x
    have h := compile_ok C.gates C.output ws x good
    have start : ws.map (val x) = List.ofFn x := by simp [ws,List.map_ofFn,Function.comp_def]
    rw [start] at h
    change eval (compile C.gates C.output ws) x = true ↔ active G x
    rw [h]; exact rep x
  have count := bound_aux (edges G + cost p) G p (Nat.le_refl _) hs sq representsP
  have sub : positions C.gates ⊆ A := by
    intro j h
    obtain ⟨g,atJ,op⟩ := pos_valid _ _ h
    exact incl j g atJ op
  have hc : cost p = nOr C.gates := compile_cost ..
  have ha := Finset.card_le_card sub
  rw [pos_count] at ha
  omega

end PEqualNP.Outside.Meta599

namespace PEqualNP.Outside

theorem L_meta_599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → G.edgeSet.ncard ≤ A.card + 1 := by
  intro n G C A hs h4 hm rep incl
  exact Meta599.fromCircuit n G C A hs (Meta599.sq_of_walk G h4) hm rep incl

end PEqualNP.Outside
