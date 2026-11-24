import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1723

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (W gs x).getD t false = true → (W gs y).getD t false = true

lemma mono_nil {n : ℕ} : Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := ofFn_getD_true x t ht
  exact (ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

lemma mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Mono (n := n) gs) :
    Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [W_val] at ht ⊢
  by_cases htt : t = n + gs.length
  · rw [if_pos htt] at ht ⊢
    rcases hop with hand | hor
    · rw [hand] at ht ⊢
      exact (all_true _ _).mpr (fun i hi => h x y hxy i ((all_true _ _).mp ht i hi))
    · rw [hor] at ht ⊢
      obtain ⟨i, hi, hti⟩ := (any_true _ _).mp ht
      exact (any_true _ _).mpr ⟨i, hi, h x y hxy i hti⟩
  · rw [if_neg htt] at ht ⊢
    exact h x y hxy t ht

lemma mono_all {n : ℕ} (gs : List Gate) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => intro _; exact mono_nil
  | append_singleton l a ih =>
    intro h
    exact mono_step l a (h a (by simp)) (ih (fun g hg => h g (by simp [hg])))

lemma eval_mono {n : ℕ} (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hx : Circuit.eval ⟨gs, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn y) = true :=
  mono_all gs h x y hxy o hx


open PEqualNP.MetaComplexity Finset
abbrev ev {N : ℕ} (C : Circuit) (X Y : Finset (Fin N)) :=
  circuitFun (N+N) C (Fin.append (fun u => decide (u ∈ X)) (fun t => decide (t ∈ Y)))
abbrev edges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (S W : Finset (Fin N)) :=
  ((S ×ˢ W).filter (fun z => I z.1 z.2)).card
lemma pinned {N : ℕ} (S W T X Y : Finset (Fin N)) (hx : X ⊆ S) (hy : Y ⊆ W) (hw : Disjoint W T) :
    Fin.append (fun u => decide (u ∈ S) && decide (u ∈ X)) (fun t => if t ∈ W then decide (t ∈ Y) else decide (t ∈ T)) =
    Fin.append (fun u => decide (u ∈ X)) (fun t => decide (t ∈ Y ∪ T)) := by
  congr 1
  · funext u; by_cases h : u ∈ X <;> simp [h,fun hu => hx hu]
  · funext t
    by_cases h : t ∈ W
    · have ht : t ∉ T := fun z => Finset.disjoint_left.mp hw h z
      simp [h,ht]
    · have ht : t ∉ Y := fun z => h (hy z)
      simp [h,ht]

lemma edge_input {N : ℕ} (p l : Fin N) :
    (fun i : Fin (N+N) => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) =
    Fin.append (fun u => decide (u ∈ ({p} : Finset _))) (fun t => decide (t ∈ ({l} : Finset _))) := by
  funext i
  refine Fin.addCases (m:=N) (n:=N) (fun u => ?_) (fun t => ?_) i
  · rw [Fin.append_left]; simp [Fin.ext_iff]; omega
  · rw [Fin.append_right]; simp [Fin.ext_iff]; omega

lemma ev_up {N : ℕ} {C : Circuit} (op : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length=2)
    {X Y Z : Finset (Fin N)} (sub : Y ⊆ Z) (on : ev C X Y=true) : ev C X Z=true := by
  apply eval_mono C.gates C.output (fun g hg => (op g hg).1) _ _ _ on
  intro i
  refine Fin.addCases (m:=N) (n:=N) (fun u => ?_) (fun t => ?_) i
  · simp
  · rw [Fin.append_right,Fin.append_right]; simpa using (fun h : t∈Y => sub h)
end PEqualNP.Outside.L_meta_1723

namespace PEqualNP.Outside.L_meta_1723
open Finset
abbrev nb {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (p : Fin N) := univ.filter (I p)
abbrev surv {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (p : Fin N) (T : Finset (Fin N)) :=
  univ.filter (fun u => u ≠ p ∧ ∀ l ∈ T, ¬ I u l)
abbrev avail {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (p : Fin N) (T : Finset (Fin N)) :=
  univ.filter (fun l => ¬ I p l ∧ l ∉ T)

lemma row_regular {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 1 ≤ q)
    (hn : N=q^2+q+1) (col : ∀ l, (univ.filter (fun p => I p l)).card=q+1)
    (pair : ∀ p u, p≠u → ∃! l, I p l ∧ I u l) (p : Fin N) : (nb I p).card=q+1 := by
  classical
  let f := fun l => (univ.filter (fun u => I u l)).erase p
  have cover : univ.erase p = (nb I p).biUnion f := by
    ext u
    simp only [mem_erase,mem_univ,and_true,mem_biUnion,mem_filter,true_and,f]
    constructor
    · intro h
      obtain ⟨l,⟨a,b⟩,_⟩ := pair p u (Ne.symm h)
      exact ⟨l,a,h,b⟩
    · rintro ⟨_,_,h,_⟩;exact h
  have dis : (nb I p : Set _).PairwiseDisjoint f := by
    intro l hl k hk ne
    apply Finset.disjoint_left.mpr
    intro u hu ku
    obtain ⟨hnp,hi⟩ := mem_erase.mp hu
    exact ne ((pair p u (Ne.symm hnp)).unique ⟨(mem_filter.mp hl).2,(mem_filter.mp hi).2⟩
      ⟨(mem_filter.mp hk).2,(mem_filter.mp (mem_erase.mp ku).2).2⟩)
  have cardf : ∀ l ∈ nb I p, (f l).card=q := by
    intro l hl
    dsimp [f]
    have hp : p ∈ univ.filter (fun u => I u l) := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hl).2⟩
    rw [card_erase_of_mem hp,col]
    omega
  have eq := congrArg Finset.card cover
  rw [card_biUnion dis,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at eq
  simp_rw [sum_congr rfl cardf,sum_const,smul_eq_mul] at eq
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [←eq,hn]
  rw [Nat.add_sub_cancel];ring

lemma pair_unique_dual {N : ℕ} {I : Fin N → Fin N → Prop}
    (h : ∀ p u, p≠u → ∃! l, I p l ∧ I u l) (l k : Fin N) (ne : l≠k)
    {a b : Fin N} (ha : I a l ∧ I a k) (hb : I b l ∧ I b k) : a=b := by
  by_contra ab
  exact ne ((h a b ab).unique ⟨ha.1,hb.1⟩ ⟨ha.2,hb.2⟩)

lemma numeric {N q d s w e : ℕ} (qn : 8 ≤ q) (hn : N=q^2+q+1)
    (dq : 4*d ≤ q) (removed : N ≤ s + 1+d*(q+1)) (sw : w ≤ N) (inc : q*s ≤ e) :
    N*q+2*(s+w) ≤ 2*e := by
  have hs : 3*(N-1) ≤ 4*s := by
    have t := Nat.mul_le_mul_right (q+1) dq
    rw [hn,Nat.add_sub_cancel] at *
    nlinarith
  have Ns : N ≥ 3*q := by nlinarith [Nat.mul_self_le_mul_self qn, Nat.mul_le_mul_right q qn]
  have nq : 7*N+3*(q-1) ≤ q*N := by nlinarith [Nat.mul_le_mul_right N qn, Nat.sub_le q 1]
  have hcancel : (q-1)+1=q := by omega
  have hncan : (N-1)+1=N := by omega
  nlinarith [Nat.mul_le_mul_right (q-1) hs,congrArg (fun x => x*N) hcancel,congrArg (fun x => x*(q-1)) hncan]

lemma dense {N q d : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (qn : 8 ≤ q) (hn : N=q^2+q+1) (dq : 4*d ≤ q)
    (row : ∀ p, (nb I p).card=q+1) (col : ∀ l, (univ.filter (fun p => I p l)).card=q+1)
    (uniq : ∀ u p, u≠p → ∀ l k, I u l ∧ I p l → I u k ∧ I p k → l=k)
    (p : Fin N) (T : Finset (Fin N)) (ht : T.card≤d) :
    N*q+2*((surv I p T).card+(avail I p T).card) ≤
      2*(((surv I p T ×ˢ avail I p T).filter (fun z => I z.1 z.2)).card) := by
  classical
  let S := surv I p T
  let W := avail I p T
  have cover : (univ : Finset (Fin N)) ⊆ S ∪ insert p (T.biUnion (fun l => univ.filter (fun x => I x l))) := by
    intro u _
    by_cases h : u∈S
    · exact mem_union_left _ h
    · simp [S,surv] at h
      by_cases e : u=p
      · simp [e]
      · obtain ⟨l,hl,hi⟩ := h e
        exact mem_union_right _ (mem_insert_of_mem (mem_biUnion.mpr ⟨l,hl,by simp [hi]⟩))
  have removed : N ≤ S.card + 1+d*(q+1) := by
    have a := (card_le_card cover).trans (card_union_le ..)
    have b := card_insert_le p (T.biUnion (fun l => univ.filter (fun x => I x l)))
    have c := card_biUnion_le (s:=T) (t:=fun l => univ.filter (fun x => I x l))
    simp only [col,sum_const,smul_eq_mul,card_univ,Fintype.card_fin] at *
    have := Nat.mul_le_mul_right (q+1) ht
    omega
  apply numeric qn hn dq removed (by simpa using W.card_le_univ)
  have each (u : Fin N) (hu : u∈S) : q ≤ (W.filter (I u)).card := by
    let lost := (nb I u).filter (I p)
    have small : lost.card ≤ 1 := by
      apply card_le_one.mpr
      intro l hl k hk
      exact uniq u p (mem_filter.mp hu).2.1 l k
        ⟨(mem_filter.mp (mem_filter.mp hl).1).2,(mem_filter.mp hl).2⟩
        ⟨(mem_filter.mp (mem_filter.mp hk).1).2,(mem_filter.mp hk).2⟩
    have sub : nb I u ⊆ W.filter (I u) ∪ lost := by
      intro l hl
      by_cases ip : I p l
      · exact mem_union_right _ (mem_filter.mpr ⟨hl,ip⟩)
      · have notT := fun (v : l∈T) => (mem_filter.mp hu).2.2 _ v (mem_filter.mp hl).2
        exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ip,notT⟩,(mem_filter.mp hl).2⟩)
    have := (card_le_card sub).trans (card_union_le ..)
    rw [row] at this;omega
  change q*S.card ≤ ((S ×ˢ W).filter (fun z => I z.1 z.2)).card
  rw [Finset.card_filter (fun z : Fin N × Fin N => I z.1 z.2) (S ×ˢ W),Finset.sum_product]
  simp_rw [←Finset.card_filter]
  simpa only [sum_const,smul_eq_mul,Nat.mul_comm] using (Finset.sum_le_sum each)

end PEqualNP.Outside.L_meta_1723

open PEqualNP.Outside.L_meta_1723 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.L_meta_1723 : (∀ (N8 K8 : ℕ) (I8 : Fin N8 → Fin N8 → Prop) [DecidableRel I8] (Ca8 Cb8 : PEqualNP.CircuitLowerBounds.Circuit) (S8 W8 : Finset (Fin N8)), (∀ g8 ∈ Ca8.gates, (g8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Ca8 → (∀ g8a ∈ Cb8.gates, (g8a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8a.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Cb8 → (∀ X8 Y8 : Finset (Fin N8), X8 ⊆ S8 → Y8 ⊆ W8 → Y8.card ≤ K8 → (∀ p8 ∈ X8, ∀ l8 ∈ Y8, ¬ I8 p8 l8) → (PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8 => decide (a8 ∈ X8)) (fun b8 => decide (b8 ∈ Y8))) && PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8a => decide (a8a ∈ X8)) (fun b8a => decide (b8a ∈ Y8)))) = false) → (∀ pz8 ∈ S8, ∀ T8 ⊆ W8, (∀ l8a ∈ T8, ¬ I8 pz8 l8a) → T8.card ≤ K8 → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8b => decide (a8b ∈ ({pz8} : Finset (Fin N8)))) (fun b8b => decide (b8b ∈ T8))) = true → ∀ X8a Y8a : Finset (Fin N8), X8a ⊆ S8.filter (fun u8 => u8 ≠ pz8 ∧ ∀ l8b ∈ T8, ¬ I8 u8 l8b) → Y8a ⊆ W8.filter (fun l8c => ¬ I8 pz8 l8c ∧ l8c ∉ T8) → Y8a.card + T8.card ≤ K8 → (∀ p8a ∈ X8a, ∀ l8d ∈ Y8a, ¬ I8 p8a l8d) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8c => decide (a8c ∈ X8a)) (fun b8c => decide (b8c ∈ (Y8a ∪ T8)))) = false) ∧ (∀ wz8 ∈ W8, ∀ Q8 ⊆ S8, (∀ p8b ∈ Q8, ¬ I8 p8b wz8) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8d => decide (a8d ∈ Q8)) (fun b8d => decide (b8d ∈ ({wz8} : Finset (Fin N8))))) = true → ∀ X8b Y8b : Finset (Fin N8), X8b ⊆ S8.filter (fun u8a => ¬ I8 u8a wz8 ∧ u8a ∉ Q8) → Y8b ⊆ W8.filter (fun l8e => l8e ≠ wz8 ∧ ∀ p8c ∈ Q8, ¬ I8 p8c l8e) → Y8b.card + 1 ≤ K8 → (∀ p8e ∈ X8b, ∀ l8f ∈ Y8b, ¬ I8 p8e l8f) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8e => decide (a8e ∈ X8b)) (fun b8e => decide (b8e ∈ (insert wz8 Y8b)))) = false)) → (∀ (q90 N90 a90 b90 : ℕ) (I90 : Fin N90 → Fin N90 → Prop) [DecidableRel I90] (D90 : PEqualNP.CircuitLowerBounds.Circuit) (S90 W90 : Finset (Fin N90)) (nu90 : Fin N90 → Bool), 2 ≤ q90 → N90 = q90 ^ 2 + q90 + 1 → (∀ l90c : Fin N90, (Finset.univ.filter (fun p90c => I90 p90c l90c)).card = q90 + 1) → (∀ pa90 pb90 : Fin N90, pa90 ≠ pb90 → ∃! lb90 : Fin N90, I90 pa90 lb90 ∧ I90 pb90 lb90) → (∀ g90 ∈ D90.gates, (g90.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g90.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g90.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N90 + N90) D90 → (∀ j90 < D90.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i90 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).inputs, (D90.lineDegrees (N90 + N90) (Finset.Ico N90 (N90 + N90))).getD i90 0 = 0) ∨ (∀ h90 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).inputs, (D90.lineDegrees (N90 + N90) (Finset.range N90)).getD h90 0 = 0)) → 1 ≤ a90 → 1 ≤ b90 → (∀ p90 ∈ S90, ∀ l90 ∈ W90, I90 p90 l90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90 => decide (u90 ∈ S90) && decide (u90 = p90)) (fun t90 => if t90 ∈ W90 then decide (t90 = l90) else nu90 t90)) = true) → (∀ p90a ∈ S90, ∀ T90 ⊆ W90, (∀ l90a ∈ T90, ¬ I90 p90a l90a) → T90.card ≤ a90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90a => decide (u90a ∈ S90) && decide (u90a = p90a)) (fun t90a => if t90a ∈ W90 then decide (t90a ∈ T90) else nu90 t90a)) = false) → (∀ l90b ∈ W90, ∀ X90 ⊆ S90, (∀ p90b ∈ X90, ¬ I90 p90b l90b) → X90.card ≤ b90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90b => decide (u90b ∈ S90) && decide (u90b ∈ X90)) (fun t90b => if t90b ∈ W90 then decide (t90b = l90b) else nu90 t90b)) = false) → min (min a90 b90) q90 * ((S90 ×ˢ W90).filter (fun pl90 => I90 pl90.1 pl90.2)).card ≤ 5 * q90 * D90.size + min (min a90 b90) q90 * (S90.card + W90.card)) → ∀ (q9 N9 k9 : ℕ) (I9 : Fin N9 → Fin N9 → Prop) [DecidableRel I9] (Ca9 Cb9 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q9 → N9 = q9 ^ 2 + q9 + 1 → (∀ l9a : Fin N9, (Finset.univ.filter (fun p9a => I9 p9a l9a)).card = q9 + 1) → (∀ pa9 pb9 : Fin N9, pa9 ≠ pb9 → ∃! lb9 : Fin N9, I9 pa9 lb9 ∧ I9 pb9 lb9) → 8 ≤ q9 → 2 ≤ k9 → (∀ g9 ∈ Ca9.gates, (g9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g9.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g9.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N9 + N9) Ca9 → (∀ g9a ∈ Cb9.gates, (g9a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g9a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g9a.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N9 + N9) Cb9 → (∀ j9 < Ca9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt Ca9 j9).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i9b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Ca9 j9).inputs, (Ca9.lineDegrees (N9 + N9) (Finset.Ico N9 (N9 + N9))).getD i9b 0 = 0) ∨ (∀ h9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Ca9 j9).inputs, (Ca9.lineDegrees (N9 + N9) (Finset.range N9)).getD h9 0 = 0)) → (∀ j9a < Cb9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt Cb9 j9a).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i9c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Cb9 j9a).inputs, (Cb9.lineDegrees (N9 + N9) (Finset.Ico N9 (N9 + N9))).getD i9c 0 = 0) ∨ (∀ h9a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Cb9 j9a).inputs, (Cb9.lineDegrees (N9 + N9) (Finset.range N9)).getD h9a 0 = 0)) → (∀ p9 l9 : Fin N9, I9 p9 l9 → (PEqualNP.MetaComplexity.circuitFun (N9 + N9) Ca9 (fun i9 => decide (i9 = Fin.castAdd N9 p9 ∨ i9 = Fin.natAdd N9 l9)) && PEqualNP.MetaComplexity.circuitFun (N9 + N9) Cb9 (fun i9a => decide (i9a = Fin.castAdd N9 p9 ∨ i9a = Fin.natAdd N9 l9))) = true) → (∀ z9 : Fin (N9 + N9) → Bool, (Finset.univ.filter (fun l9b : Fin N9 => z9 (Fin.natAdd N9 l9b) = true)).card ≤ k9 → (¬ ∃ p9b l9c : Fin N9, I9 p9b l9c ∧ z9 (Fin.castAdd N9 p9b) = true ∧ z9 (Fin.natAdd N9 l9c) = true) → (PEqualNP.MetaComplexity.circuitFun (N9 + N9) Ca9 z9 && PEqualNP.MetaComplexity.circuitFun (N9 + N9) Cb9 z9) = false) → N9 * min (k9 / 2) (q9 / 4) ≤ 10 * max Ca9.size Cb9.size := by
  intro spill sigma q N k I inst A B q2 plane col pair q8 k2 aops aback bops bback akm bkm bothOn bothOff
  classical
  let d := min (k/2) (q/4)
  have d1 : 1 ≤ d := by dsimp [d];omega
  have dk : 2*d ≤ k := by dsimp [d];omega
  have dq : 4*d ≤ q := by dsimp [d];omega
  have dm : min (min d d) q = d := by omega
  have row := row_regular I (by omega) plane col pair
  have un (p l : Fin N) (h : I p l) : ev A {p} {l}=true ∧ ev B {p} {l}=true := by
    have h1 := bothOn p l h
    rw [edge_input p l] at h1
    exact Bool.and_eq_true_iff.mp h1
  have safe (X Y : Finset (Fin N)) (h : Y.card ≤ k) (no : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) :
      (ev A X Y && ev B X Y) = false := by
    apply bothOff
    · simpa only [Fin.append_right,decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter] using h
    · simpa only [Fin.append_left,Fin.append_right,decide_eq_true_eq,not_exists,not_and] using
        (show ∀ p l, I p l → p ∈ X → l ∈ Y → False from fun p l e px ly => no p px l ly e)
  have useRegion (D : Circuit)
      (ops : ∀ g ∈ D.gates,(g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length=2)
      (back : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) D)
      (km : ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        (∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs,
          (D.lineDegrees (N+N) (Finset.Ico N (N+N))).getD i 0 = 0) ∨
        (∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs,
          (D.lineDegrees (N+N) (Finset.range N)).getD i 0 = 0))
      (Dle : D.size ≤ max A.size B.size)
      (S W T : Finset (Fin N)) (dis : Disjoint W T)
      (dens : N*q+2*(S.card+W.card) ≤ 2*edges I S W)
      (pos : ∀ p ∈ S, ∀ l ∈ W, I p l → ev D {p} ({l} ∪ T) = true)
      (rp : ∀ p ∈ S, ∀ Y ⊆ W, (∀ l ∈ Y, ¬ I p l) → Y.card ≤ d → ev D {p} (Y∪T) = false)
      (cp : ∀ l ∈ W, ∀ X ⊆ S, (∀ p ∈ X, ¬ I p l) → X.card ≤ d → ev D X ({l}∪T) = false) :
      N*d ≤ 10*max A.size B.size := by
    have bound := sigma q N d d I D S W (fun t => decide (t∈T)) q2 plane col pair ops back km d1 d1
      (fun p hp l hl e => by
        have eq := pinned S W T {p} {l} (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl) dis
        simp only [Finset.mem_singleton] at eq
        rw [eq]
        simpa only [ev,Finset.mem_singleton] using pos p hp l hl e)
      (fun p hp Y hy no lim => by
        have eq := pinned S W T {p} Y (Finset.singleton_subset_iff.mpr hp) hy dis
        simp only [Finset.mem_singleton] at eq
        rw [eq]
        simpa only [ev,Finset.mem_singleton] using rp p hp Y hy no lim)
      (fun l hl X hx no lim => by
        have eq := pinned S W T X {l} hx (Finset.singleton_subset_iff.mpr hl) dis
        simp only [Finset.mem_singleton] at eq
        rw [eq]
        simpa only [ev,Finset.mem_singleton] using cp l hl X hx no lim)
    rw [dm] at bound
    change d*edges I S W ≤ 5*q*D.size+d*(S.card+W.card) at bound
    apply Nat.le_of_mul_le_mul_right (c:=q) _ (by omega)
    nlinarith [Nat.mul_le_mul_left d dens,Nat.mul_le_mul_left (10*q) Dle]
  let U : Finset (Fin N) := Finset.univ
  have past := spill N k I A B U U aops aback bops bback (fun X Y _ _ hy no => safe X Y hy no)
  have drow (p : Fin N) (T : Finset (Fin N)) (lim : T.card ≤ d) :=
    dense I q8 plane dq row col (fun u v ne l j h1 h2 => (pair u v ne).unique h1 h2) p T lim
  let J := fun l p : Fin N => I p l
  have dcol (l : Fin N) (Q : Finset (Fin N)) (lim : Q.card ≤ d) :=
    dense J q8 plane dq col row (fun a b ne x y h1 h2 => pair_unique_dual pair a b ne h1 h2) l Q lim
  have apos (S W T : Finset (Fin N)) (p : Fin N) (_ : p∈S) (l : Fin N) (_ : l∈W) (e : I p l) :
      ev A {p} ({l}∪T)=true := ev_up aops Finset.subset_union_left (un p l e).1
  by_cases goodP : ∀ p : Fin N, ∀ Y : Finset (Fin N), (∀ l ∈ Y, ¬ I p l) → Y.card ≤ d → ev B {p} Y=false
  · by_cases goodL : ∀ l : Fin N, ∀ X : Finset (Fin N), (∀ p ∈ X, ¬ I p l) → X.card ≤ d → ev B X {l}=false
    · apply useRegion B bops bback bkm (le_max_right ..) U U ∅ (by simp)
      · have counts : edges I U U=N*(q+1) := by
          unfold edges
          rw [Finset.card_filter,Finset.sum_product]
          simp_rw [←Finset.card_filter]
          change (∑ p : Fin N, (nb I p).card) = N*(q+1)
          simp [row]
        rw [counts]
        simp only [U,Finset.card_univ,Fintype.card_fin]
        nlinarith [Nat.mul_le_mul_right N q8]
      · intro p _ l _ h; simpa using (un p l h).2
      · intro p _ Y _ h lim; simpa using goodP p Y h lim
      · intro l _ X _ h lim; simpa using goodL l X h lim
    · push_neg at goodL
      obtain ⟨l,Q,no,lim,on⟩ := goodL
      have spillL := past.2 l (Finset.mem_univ _) Q (Finset.subset_univ _) no (by simpa [ev] using on)
      let S := avail J l Q
      let W := surv J l Q
      have rwE : edges I S W = edges J W S := by
        unfold edges
        simp only [Finset.card_filter,Finset.sum_product]
        exact Finset.sum_comm
      apply useRegion A aops aback akm (le_max_left ..) S W {l}
      · apply Finset.disjoint_left.mpr
        intro z hz hl
        exact (Finset.mem_filter.mp hz).2.1 (Finset.mem_singleton.mp hl)
      · rw [rwE,add_comm S.card W.card]
        exact dcol l Q lim
      · exact apos S W {l}
      · intro p hp Y hy neg limY
        have w := spillL {p} Y (Finset.singleton_subset_iff.mpr hp) hy (by omega)
          (by intro x hx; exact (Finset.mem_singleton.mp hx).symm ▸ neg)
        simpa [ev,Finset.union_comm,Bool.or_comm] using w
      · intro j hj X hx neg limX
        have w := spillL X {j} hx (Finset.singleton_subset_iff.mpr hj) (by simp;omega)
          (by intro p hp z hz; simpa only [Finset.mem_singleton.mp hz] using neg p hp)
        simpa [ev,Finset.union_comm,Bool.or_comm] using w
  · push_neg at goodP
    obtain ⟨p,T,no,lim,on⟩ := goodP
    have spillP := past.1 p (Finset.mem_univ _) T (Finset.subset_univ _) no (by omega) (by simpa [ev] using on)
    let S := surv I p T
    let W := avail I p T
    apply useRegion A aops aback akm (le_max_left ..) S W T
    · exact Finset.disjoint_left.mpr (fun a h => (Finset.mem_filter.mp h).2.2)
    · exact drow p T lim
    · exact apos S W T
    · intro z hz Y hy neg limY
      apply spillP {z} Y (Finset.singleton_subset_iff.mpr hz) hy (by omega)
      intro v hv
      exact (Finset.mem_singleton.mp hv).symm ▸ neg
    · intro j hj X hx neg limX
      apply spillP X {j} hx (Finset.singleton_subset_iff.mpr hj) (by simp;omega)
      intro v hv z hz
      simpa only [Finset.mem_singleton.mp hz] using neg v hv
