import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3497

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- The clause set of a gate from the clause sets of its two inputs.
def comb {n : ℕ} (op : GateOp) (A B : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  if op.eval [false, true] = true then A.biUnion (fun c => B.image (fun d => c ∪ d)) else A ∪ B

def kstep (n : ℕ) (K : List (Finset (Finset (Fin n)))) (g : Gate) :
    List (Finset (Finset (Fin n))) :=
  K ++ [comb g.op (K.getD (g.inputs.getD 0 0) {∅}) (K.getD (g.inputs.getD 1 0) {∅})]

def init (n : ℕ) : List (Finset (Finset (Fin n))) := List.ofFn fun i : Fin n => {{i}}

def W (gs : List Gate) (k : ℕ) (x : List Bool) : List Bool := (gs.take k).foldl stp x

def Kf (n : ℕ) (gs : List Gate) (k : ℕ) : List (Finset (Finset (Fin n))) :=
  (gs.take k).foldl (kstep n) (init n)

theorem W_succ (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : List Bool) :
    W gs (k + 1) x = stp (W gs k x) gs[k] := by
  unfold W
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

theorem Kf_succ (n : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    Kf n gs (k + 1) = kstep n (Kf n gs k) gs[k] := by
  unfold Kf
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

theorem W_length (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length) (x : List Bool) :
    (W gs k x).length = x.length + k := by
  induction k with
  | zero => simp [W]
  | succ k ih =>
    rw [W_succ gs k (by omega), stp, List.length_append, ih (by omega)]
    simp; omega

theorem Kf_length (n : ℕ) (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length) :
    (Kf n gs k).length = n + k := by
  induction k with
  | zero => simp [Kf, init]
  | succ k ih =>
    rw [Kf_succ n gs k (by omega), kstep, List.length_append, ih (by omega)]
    simp; omega

theorem Kf_stable (n : ℕ) (gs : List Gate) (k : ℕ) (i : ℕ) (hi : i < n + k) :
    ∀ m, k ≤ m → m ≤ gs.length → (Kf n gs m).getD i {∅} = (Kf n gs k).getD i {∅} := by
  intro m
  induction m with
  | zero => intro h _; have : k = 0 := by omega
            subst this; rfl
  | succ m ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with e | h1
    · rw [e]
    · rw [Kf_succ n gs m (by omega), kstep,
        List.getD_append _ _ _ _ (by rw [Kf_length n gs m (by omega)]; omega)]
      exact ih (by omega) (by omega)

-- A clause set is satisfied by x when every clause has a true variable.
def Sat {n : ℕ} (x : List Bool) (K : Finset (Finset (Fin n))) : Prop :=
  ∀ c ∈ K, ∃ v ∈ c, x.getD (v : ℕ) false = true

theorem sat_union {n : ℕ} (x : List Bool) (A B : Finset (Finset (Fin n))) :
    Sat x (A ∪ B) ↔ Sat x A ∧ Sat x B := by
  unfold Sat
  constructor
  · intro h; exact ⟨fun c hc => h c (Finset.mem_union_left _ hc),
      fun c hc => h c (Finset.mem_union_right _ hc)⟩
  · rintro ⟨h1, h2⟩ c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem sat_prod {n : ℕ} (x : List Bool) (A B : Finset (Finset (Fin n))) :
    Sat x (A.biUnion (fun c => B.image (fun d => c ∪ d))) ↔ Sat x A ∨ Sat x B := by
  unfold Sat
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨⟨c1, hc1, h1⟩, ⟨c2, hc2, h2⟩⟩ := hc
    obtain ⟨v, hv, hx⟩ := h (c1 ∪ c2) (Finset.mem_biUnion.mpr ⟨c1, hc1,
      Finset.mem_image.mpr ⟨c2, hc2, rfl⟩⟩)
    rcases Finset.mem_union.mp hv with hv | hv
    · exact absurd hx (by simpa using h1 v hv)
    · exact absurd hx (by simpa using h2 v hv)
  · intro h c hc
    obtain ⟨c1, hc1, hc'⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨c2, hc2, rfl⟩ := Finset.mem_image.mp hc'
    rcases h with h | h
    · obtain ⟨v, hv, hx⟩ := h c1 hc1
      exact ⟨v, Finset.mem_union_left _ hv, hx⟩
    · obtain ⟨v, hv, hx⟩ := h c2 hc2
      exact ⟨v, Finset.mem_union_right _ hv, hx⟩

theorem sat_empty {n : ℕ} (x : List Bool) : ¬ Sat x ({∅} : Finset (Finset (Fin n))) := by
  intro h
  obtain ⟨v, hv, _⟩ := h ∅ (Finset.mem_singleton_self _)
  simp at hv

theorem semantic (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b])
    (x : List Bool) (hx : x.length = n) :
    ∀ k, k ≤ gs.length → ∀ w, (W gs k x).getD w false = true ↔ Sat x ((Kf n gs k).getD w {∅}) := by
  intro k
  induction k with
  | zero =>
    intro _ w
    simp only [W, Kf, List.take_zero, List.foldl_nil]
    by_cases hw : w < n
    · have e : (init n).getD w {∅} = {{⟨w, hw⟩}} := by
        simp [init, List.getD_eq_getElem?_getD, hw]
      rw [e]
      simp [Sat]
    · rw [List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by simp [init]; omega)]
      simp only [Bool.false_eq_true, false_iff]
      exact sat_empty x
  | succ k ih =>
    intro hk w
    have hk' : k < gs.length := by omega
    have lW := W_length gs k (by omega) x
    have lK := Kf_length n gs k (by omega)
    rw [W_succ gs k hk', Kf_succ n gs k hk', stp, kstep]
    rcases Nat.lt_trichotomy w (n + k) with h | h | h
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ih (by omega) w
    · subst h
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [lW, lK, hx, Nat.sub_self, List.getD_cons_zero]
      obtain ⟨hop, a, b, hab⟩ := hg _ (List.getElem_mem hk')
      rw [hab]
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
      have ha := ih (by omega) a
      have hb := ih (by omega) b
      rcases hop with hop | hop
      · have hc : comb gs[k].op ((Kf n gs k).getD a {∅}) ((Kf n gs k).getD b {∅}) =
            (Kf n gs k).getD a {∅} ∪ (Kf n gs k).getD b {∅} := by
          simp [comb, hop, GateOp.eval]
        rw [hc, sat_union, hop, ← ha, ← hb]
        simp [GateOp.eval]
      · have hc : comb gs[k].op ((Kf n gs k).getD a {∅}) ((Kf n gs k).getD b {∅}) =
            ((Kf n gs k).getD a {∅}).biUnion
              (fun c => ((Kf n gs k).getD b {∅}).image (fun d => c ∪ d)) := by
          simp [comb, hop, GateOp.eval]
        rw [hc, sat_prod, hop, ← ha, ← hb]
        simp [GateOp.eval]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      simp only [Bool.false_eq_true, false_iff]
      exact sat_empty x

end PEqualNP.Outside.L_meta_3497

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3497

theorem PEqualNP.Outside.L_meta_3497 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x4]? = Option.some x5 → ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 < x8 ∧ x8 < x1 + x4) → ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : ℕ) (x7 : x6 < x2.size), ∃ (x8 : ℕ) (x9 : ℕ), x2.gates[x6].inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x6 ∧ x5 (x1 + x6) = if x2.gates[x6].op.eval [Bool.false, Bool.true] = Bool.true then (x5 x8).biUnion fun (x10 : Finset (Fin x1)) => Finset.image (fun (x11 : Finset (Fin x1)) => x10 ∪ x11) (x5 x9) else x5 x8 ∪ x5 x9) ∧ ∀ (x6 : List Bool), x6.length = x1 → ∀ (x8 : ℕ), (x2.wires x6).getD x8 Bool.false = Bool.true ↔ ∀ x9 ∈ x5 x8, ∃ x11 ∈ x9, x6.getD (↑x11) Bool.false = Bool.true := by
  intro n C hmono hshape
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨a, b, hab, _⟩ := hshape j C.gates[j] (List.getElem?_eq_getElem hj)
    refine ⟨?_, a, b, hab⟩
    have := (hmono _ hg).1
    simpa using this
  refine ⟨fun w => (Kf n C.gates C.gates.length).getD w {∅}, ?_, ?_, ?_⟩
  · intro i
    show (Kf n C.gates C.gates.length).getD i {∅} = {{i}}
    rw [Kf_stable n C.gates 0 i (by omega) _ (Nat.zero_le _) le_rfl]
    simp [Kf, init, List.getD_eq_getElem?_getD]
  · intro j hj
    obtain ⟨a, b, hab, hlt, hb⟩ := hshape j C.gates[j] (List.getElem?_eq_getElem hj)
    refine ⟨a, b, hab, hlt, hb, ?_⟩
    have hj' : j < C.gates.length := hj
    show (Kf n C.gates C.gates.length).getD (n + j) {∅} = comb C.gates[j].op
      ((Kf n C.gates C.gates.length).getD a {∅}) ((Kf n C.gates C.gates.length).getD b {∅})
    rw [Kf_stable n C.gates (j + 1) (n + j) (by omega) _ (by omega) le_rfl,
      Kf_stable n C.gates j a (by omega) _ (by omega) le_rfl,
      Kf_stable n C.gates j b (by omega) _ (by omega) le_rfl,
      Kf_succ n C.gates j hj', kstep,
      List.getD_append_right _ _ _ _ (by rw [Kf_length n C.gates j (by omega)])]
    rw [Kf_length n C.gates j (by omega), Nat.sub_self, List.getD_cons_zero]
    have hab' : (C.gates[j]'hj').inputs = [a, b] := hab
    rw [hab']
    rfl
  · intro x hx w
    have h := semantic n C.gates hg x hx C.gates.length le_rfl w
    have e : W C.gates C.gates.length x = C.wires x := by
      unfold W Circuit.wires
      rw [List.take_length]
      rfl
    rw [e] at h
    exact h
