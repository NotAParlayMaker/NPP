import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4717

open PEqualNP.CircuitLowerBounds

def Pre {m : ℕ} (x6 x7 : List (Fin m → Bool)) : Prop :=
  ∀ (k : ℕ) (hk : k < x7.length), ∃ a ∈ x6 ++ x7.take k, ∃ b ∈ x6 ++ x7.take k, ∃ c1 c2 : Bool,
    x7[k] = fun t => (a t ^^ c1) && (b t ^^ c2)

def Rep {m : ℕ} (x6 x7 : List (Fin m → Bool)) (W : Fin m → List Bool) : Prop :=
  ∀ w : ℕ, ∃ v ∈ x6 ++ x7, ∃ c : Bool, ∀ t, (W t).getD w false = (v t ^^ c)

theorem mono_snoc {m : ℕ} {x6 x7 : List (Fin m → Bool)} (n : Fin m → Bool) :
    ∀ v ∈ x6 ++ x7, v ∈ x6 ++ (x7 ++ [n]) := by
  intro v hv
  simp only [List.mem_append] at hv ⊢
  tauto

theorem Pre_snoc {m : ℕ} {x6 x7 : List (Fin m → Bool)} (h : Pre x6 x7) {a b : Fin m → Bool}
    (ha : a ∈ x6 ++ x7) (hb : b ∈ x6 ++ x7) (c1 c2 : Bool) :
    Pre x6 (x7 ++ [fun t => (a t ^^ c1) && (b t ^^ c2)]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  by_cases hlt : k < x7.length
  · obtain ⟨a', ha', b', hb', d1, d2, he⟩ := h k hlt
    have e1 : (x7 ++ [fun t => (a t ^^ c1) && (b t ^^ c2)]).take k = x7.take k :=
      List.take_append_of_le_length hlt.le
    have e2 : (x7 ++ [fun t => (a t ^^ c1) && (b t ^^ c2)])[k] = x7[k] :=
      List.getElem_append_left hlt
    rw [e1, e2]
    exact ⟨a', ha', b', hb', d1, d2, he⟩
  · have hk' : k = x7.length := by omega
    subst hk'
    have e1 : (x7 ++ [fun t => (a t ^^ c1) && (b t ^^ c2)]).take x7.length = x7 := by simp
    rw [e1]
    refine ⟨a, ha, b, hb, c1, c2, ?_⟩
    simp

theorem Rep_snoc {m : ℕ} {x6 x7 x7' : List (Fin m → Bool)} (hz : (fun _ => false) ∈ x6)
    (hsub : ∀ v ∈ x6 ++ x7, v ∈ x6 ++ x7') {W : Fin m → List Bool} {L : ℕ}
    (hL : ∀ t, (W t).length = L) (hR : Rep x6 x7 W) (nv : Fin m → Bool) (v : Fin m → Bool)
    (hv : v ∈ x6 ++ x7') (c : Bool) (hnv : ∀ t, nv t = (v t ^^ c)) :
    Rep x6 x7' (fun t => W t ++ [nv t]) := by
  intro w
  rcases lt_trichotomy w L with hw | hw | hw
  · obtain ⟨u, hu, d, hd⟩ := hR w
    refine ⟨u, hsub u hu, d, fun t => ?_⟩
    rw [List.getD_append _ _ _ _ (by rw [hL t]; exact hw)]
    exact hd t
  · refine ⟨v, hv, c, fun t => ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by have := hL t; omega)]
    have e : w - (W t).length = 0 := by have := hL t; omega
    rw [e]
    simp [hnv t]
  · refine ⟨fun _ => false, List.mem_append_left _ hz, false, fun t => ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hL t]; omega)]
    rfl

theorem const_rep {m : ℕ} {x6 x7 : List (Fin m → Bool)} (hz : (fun _ => false) ∈ x6) (k : Bool) :
    ∃ v ∈ x6 ++ x7, ∃ c : Bool, ∀ t : Fin m, k = (v t ^^ c) :=
  ⟨fun _ => false, List.mem_append_left _ hz, k, fun _ => by simp⟩

theorem gate_rep {m : ℕ} {x6 x7 : List (Fin m → Bool)} (hz : (fun _ => false) ∈ x6)
    (hP : Pre x6 x7) {W : Fin m → List Bool} (hR : Rep x6 x7 W) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) :
    ∃ x7' : List (Fin m → Bool), Pre x6 x7' ∧
      x7'.length ≤ x7.length + [g].countP (fun x8 => !x8.op.eval [false]) ∧
      (∀ v ∈ x6 ++ x7, v ∈ x6 ++ x7') ∧
      ∃ v ∈ x6 ++ x7', ∃ c : Bool, ∀ t,
        g.op.eval (g.inputs.map fun i => (W t).getD i false) = (v t ^^ c) := by
  rcases hl : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c0, rest⟩⟩⟩
  ·
    refine ⟨x7, hP, Nat.le_add_right _ _, fun v hv => hv, ?_⟩
    obtain ⟨v, hv, c, hc⟩ := const_rep (x7 := x7) hz (g.op.eval [])
    exact ⟨v, hv, c, fun t => by simpa using hc t⟩
  ·
    obtain ⟨va, hva, ca, ha⟩ := hR a
    refine ⟨x7, hP, Nat.le_add_right _ _, fun v hv => hv, ?_⟩
    rcases hop with h | h | h
    · exact ⟨va, hva, ca, fun t => by
        simp only [h, hl, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id, Bool.and_true, ha t]⟩
    · exact ⟨va, hva, ca, fun t => by
        simp only [h, hl, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id, Bool.or_false, ha t]⟩
    · refine ⟨va, hva, !ca, fun t => ?_⟩
      simp only [h, hl, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, ha t]
      cases va t <;> cases ca <;> rfl
  · obtain ⟨va, hva, ca, ha⟩ := hR a
    obtain ⟨vb, hvb, cb, hb⟩ := hR b
    rcases hop with h | h | h
    · refine ⟨x7 ++ [fun t => (va t ^^ ca) && (vb t ^^ cb)], Pre_snoc hP hva hvb ca cb, ?_,
        mono_snoc _, fun t => (va t ^^ ca) && (vb t ^^ cb), by simp, false, fun t => ?_⟩
      · simp [h, GateOp.eval]
      · simp only [h, hl, GateOp.eval, List.map_cons, List.map_nil, ha t, hb t]
        cases va t <;> cases vb t <;> cases ca <;> cases cb <;> rfl
    · refine ⟨x7 ++ [fun t => (va t ^^ !ca) && (vb t ^^ !cb)], Pre_snoc hP hva hvb (!ca) (!cb), ?_,
        mono_snoc _, fun t => (va t ^^ !ca) && (vb t ^^ !cb), by simp, true, fun t => ?_⟩
      · simp [h, GateOp.eval]
      · simp only [h, hl, GateOp.eval, List.map_cons, List.map_nil, ha t, hb t]
        cases va t <;> cases vb t <;> cases ca <;> cases cb <;> rfl
    · refine ⟨x7, hP, Nat.le_add_right _ _, fun v hv => hv, va, hva, !ca, fun t => ?_⟩
      simp only [h, hl, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, ha t]
      cases va t <;> cases ca <;> rfl
  · rw [hl] at hlen
    simp at hlen

theorem sim {m : ℕ} (x6 : List (Fin m → Bool)) (hz : (fun _ => false) ∈ x6) :
    ∀ (gs : List Gate) (W : Fin m → List Bool) (L : ℕ), (∀ t, (W t).length = L) →
      ∀ x7 : List (Fin m → Bool),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      Pre x6 x7 → Rep x6 x7 W →
      ∃ x7' : List (Fin m → Bool), Pre x6 x7' ∧
        x7'.length ≤ x7.length + gs.countP (fun x8 => !x8.op.eval [false]) ∧
        Rep x6 x7' (fun t => gs.foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W t)) := by
  intro gs
  induction gs with
  | nil =>
    intro W L _ x7 _ hP hR
    exact ⟨x7, hP, by simp, hR⟩
  | cons g gs ih =>
    intro W L hL x7 hgs hP hR
    obtain ⟨hop, hlen⟩ := hgs g List.mem_cons_self
    obtain ⟨x71, hP1, hlen1, hsub1, v, hv, c, hc⟩ := gate_rep hz hP hR g hop hlen
    have hR1 := Rep_snoc hz hsub1 hL hR
      (fun t => g.op.eval (g.inputs.map fun i => (W t).getD i false)) v hv c hc
    obtain ⟨x72, hP2, hlen2, hR2⟩ := ih
      (fun t => W t ++ [g.op.eval (g.inputs.map fun i => (W t).getD i false)]) (L + 1)
      (fun t => by simp [hL t]) x71 (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) hP1 hR1
    refine ⟨x72, hP2, ?_, hR2⟩
    have hsplit : (g :: gs).countP (fun x8 => !x8.op.eval [false]) =
        [g].countP (fun x8 => !x8.op.eval [false]) + gs.countP (fun x8 => !x8.op.eval [false]) := by
      rw [← List.countP_append]
      rfl
    rw [hsplit]
    omega

end PEqualNP.Outside.L_meta_4717

theorem PEqualNP.Outside.L_meta_4717 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin x1 → Fin x2 → Bool),   PEqualNP.MetaComplexity.FanInTwo x3 →     have x6 : List (Fin x2 → Bool) := (fun (x6 : Fin x2) => Bool.false) :: List.ofFn x4;     ∃ (x7 : List (Fin x2 → Bool)), x7.length ≤ List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => !x8.op.eval [Bool.false]) x3.gates ∧ (∀ (x8 : ℕ) (x9 : x8 < x7.length), ∃ x10 ∈ x6 ++ List.take x8 x7, ∃ x11 ∈ x6 ++ List.take x8 x7, ∃ (x12 : Bool) (x13 : Bool), x7[x8] = fun (x14 : Fin x2) => (x10 x14 ^^ x12) && (x11 x14 ^^ x13)) ∧ ∃ x8 ∈ x6 ++ x7, ∃ (x9 : Bool), ∀ (x10 : Fin x2), x3.eval (List.ofFn fun (x11 : Fin x1) => x4 x11 x10) = (x8 x10 ^^ x9) := by
  intro x1 x2 x3 x4 hF
  dsimp only
  have hz : (fun (_ : Fin x2) => false) ∈ (fun (x6 : Fin x2) => Bool.false) :: List.ofFn x4 :=
    List.mem_cons_self
  have hgs : ∀ g ∈ x3.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hF g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, hlen⟩
  have hR0 : PEqualNP.Outside.L_meta_4717.Rep ((fun (x6 : Fin x2) => Bool.false) :: List.ofFn x4) []
      (fun t => List.ofFn fun (x11 : Fin x1) => x4 x11 t) := by
    intro w
    by_cases hw : w < x1
    · refine ⟨x4 ⟨w, hw⟩, ?_, false, fun t => ?_⟩
      · simp [List.mem_ofFn]
      · simp [List.getD_eq_getElem?_getD, hw]
    · refine ⟨fun _ => false, by simp, false, fun t => ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
  have hP0 : PEqualNP.Outside.L_meta_4717.Pre
      ((fun (x6 : Fin x2) => Bool.false) :: List.ofFn x4) [] := by
    intro k hk
    simp at hk
  obtain ⟨x7, hP, hlen, hR⟩ := PEqualNP.Outside.L_meta_4717.sim _ hz x3.gates
    (fun t => List.ofFn fun (x11 : Fin x1) => x4 x11 t) x1 (fun t => by simp) [] hgs hP0 hR0
  obtain ⟨v, hv, c, hc⟩ := hR x3.output
  refine ⟨x7, by simpa using hlen, hP, v, hv, c, fun t => ?_⟩
  exact hc t
