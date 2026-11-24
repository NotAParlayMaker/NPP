import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5160

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWire_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl stepWire acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl stepWire acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : w < (stepWire acc g).length := by
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (stepWire acc g) hlt]
    simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

lemma foldl_stepWire_getD_add (gs : List Gate) (acc : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl stepWire acc).getD (acc.length + k) false =
      let pref := (gs.take k).foldl stepWire acc
      let g := gs.getD k ⟨GateOp.or, []⟩
      g.op.eval (g.inputs.map fun i => pref.getD i false) := by
  induction gs generalizing acc k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.foldl_cons, List.take_zero, List.foldl_nil, List.getD_cons_zero, add_zero]
      have hlt : acc.length < (stepWire acc g).length := by
        simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_stepWire_getD_lt gs (stepWire acc g) acc.length hlt]
      simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    | succ k =>
      simp only [List.length_cons] at hk
      have hk' : k < gs.length := by omega
      simp only [List.foldl_cons, List.take_succ_cons, List.getD_cons_succ]
      have hlen : (stepWire acc g).length = acc.length + 1 := by
        simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      have hidx : acc.length + (k + 1) = (stepWire acc g).length + k := by omega
      rw [hidx, ih (stepWire acc g) k hk']

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_stepWire_length C.gates x

lemma wires_getD_lt (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (C.wires x).getD w false = x.getD w false :=
  foldl_stepWire_getD_lt C.gates x w hw

lemma wires_getD_gate (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (n + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires x).getD i false) := by
  unfold Circuit.wires
  change (C.gates.foldl stepWire x).getD (n + k) false = _
  have hadd := foldl_stepWire_getD_add C.gates x k hk
  rw [hx] at hadd
  rw [hadd]
  dsimp only
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < n + k := hrb k hk i hi
  have hpref : ((C.gates.take k).foldl stepWire x).length = n + k := by
    rw [foldl_stepWire_length, hx, List.length_take_of_le (le_of_lt hk)]
  have hsplit : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
  change ((C.gates.take k).foldl stepWire x).getD i false = (C.gates.foldl stepWire x).getD i false
  conv_rhs => rw [hsplit, List.foldl_append]
  rw [foldl_stepWire_getD_lt (C.gates.drop k) _ i (by omega)]

lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < cs.length) :
    (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : j < (coneStep n cs g).length := by
      simp only [coneStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (coneStep n cs g) hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma foldl_coneStep_getD_add (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl (coneStep n) cs).getD (cs.length + k) [] =
      let pref := (gs.take k).foldl (coneStep n) cs
      let g := gs.getD k ⟨GateOp.or, []⟩
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + pref.length))).flatMap
        (fun w => (w - n) :: pref.getD (w - n) []) := by
  induction gs generalizing cs k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.foldl_cons, List.take_zero, List.foldl_nil, List.getD_cons_zero, add_zero]
      have hlt : cs.length < (coneStep n cs g).length := by
        simp only [coneStep, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_coneStep_getD_lt n gs (coneStep n cs g) cs.length hlt]
      simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rfl
    | succ k =>
      simp only [List.length_cons] at hk
      have hk' : k < gs.length := by omega
      dsimp only
      simp only [List.foldl_cons, List.take_succ_cons, List.getD_cons_succ]
      have hlen : (coneStep n cs g).length = cs.length + 1 := by
        simp only [coneStep, List.length_append, List.length_cons, List.length_nil]
      have hidx : cs.length + (k + 1) = (coneStep n cs g).length + k := by omega
      rw [hidx, ih (coneStep n cs g) k hk']
      rfl

lemma inCone_iff (n : ℕ) (C : Circuit) (a b : ℕ) :
    InCone n C a b ↔ b < C.gates.length ∧
      ∃ w ∈ (gateAt C b).inputs, n ≤ w ∧ w < n + b ∧ (a = w - n ∨ InCone n C a (w - n)) := by
  unfold InCone cones
  by_cases hb : b < C.gates.length
  · have hadd := foldl_coneStep_getD_add n C.gates [] b hb
    simp only [List.length_nil, zero_add] at hadd
    rw [hadd]
    have hpref : ((C.gates.take b).foldl (coneStep n) []).length = b := by
      rw [foldl_coneStep_length, List.length_nil, zero_add, List.length_take_of_le (le_of_lt hb)]
    rw [hpref]
    simp only [hb, true_and, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨w, ⟨hw_in, hw_ge, hw_lt⟩, ha⟩
      refine ⟨w, hw_in, hw_ge, hw_lt, ?_⟩
      rcases ha with rfl | hmem
      · exact Or.inl rfl
      · right
        have hsplit : C.gates = C.gates.take b ++ C.gates.drop b := (List.take_append_drop b C.gates).symm
        have hEq : (C.gates.foldl (coneStep n) []).getD (w - n) [] =
            ((C.gates.take b).foldl (coneStep n) []).getD (w - n) [] := by
          conv_lhs => rw [hsplit, List.foldl_append]
          exact foldl_coneStep_getD_lt n (C.gates.drop b) _ (w - n) (by omega)
        rwa [hEq]
    · rintro ⟨w, hw_in, hw_ge, hw_lt, ha⟩
      refine ⟨w, ⟨hw_in, hw_ge, hw_lt⟩, ?_⟩
      rcases ha with rfl | hmem
      · exact Or.inl rfl
      · right
        have hsplit : C.gates = C.gates.take b ++ C.gates.drop b := (List.take_append_drop b C.gates).symm
        rw [hsplit, List.foldl_append, foldl_coneStep_getD_lt n (C.gates.drop b) _ (w - n) (by omega)] at hmem
        exact hmem
  · have hlen : (C.gates.foldl (coneStep n) []).length = C.gates.length := by
      rw [foldl_coneStep_length, List.length_nil, zero_add]
    have hnone : (C.gates.foldl (coneStep n) []).getD b [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    rw [hnone]
    simp [hb]

lemma inCone_lt (n : ℕ) (C : Circuit) {a b : ℕ} (h : InCone n C a b) :
    a < b ∧ b < C.gates.length := by
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    rw [inCone_iff] at h
    rcases h with ⟨hb, w, _, hw_ge, hw_lt, ha⟩
    refine ⟨?_, hb⟩
    rcases ha with rfl | hsub
    · omega
    · have := ih (w - n) (by omega) hsub
      omega

lemma inCone_trans (n : ℕ) (C : Circuit) {a b c : ℕ}
    (hab : InCone n C a b) (hbc : InCone n C b c) : InCone n C a c := by
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    rw [inCone_iff] at hbc ⊢
    rcases hbc with ⟨hc, w, hw_in, hw_ge, hw_lt, hb⟩
    refine ⟨hc, w, hw_in, hw_ge, hw_lt, Or.inr ?_⟩
    rcases hb with rfl | hsub
    · exact hab
    · exact ih (w - n) (by omega) hsub

lemma inCone_exists_reader (n : ℕ) (C : Circuit) {i j : ℕ} (h : InCone n C i j) :
    ∃ k < C.gates.length, i < k ∧ k ≤ j ∧ n + i ∈ (gateAt C k).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [inCone_iff] at h
    rcases h with ⟨hj, w, hw_in, hw_ge, hw_lt, hi⟩
    rcases hi with rfl | hsub
    · refine ⟨j, hj, by omega, le_refl _, ?_⟩
      have : n + (w - n) = w := by omega
      rwa [this]
    · obtain ⟨k, hk, hik, hkw, hread⟩ := ih (w - n) (by omega) hsub
      exact ⟨k, hk, hik, by omega, hread⟩

def killGate (w0 : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if w0 ∈ g.inputs then ⟨GateOp.or, []⟩ else g
  | GateOp.or => ⟨GateOp.or, g.inputs.filter (fun u => decide (u ≠ w0))⟩
  | _ => g

def killWire (w0 : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (killGate w0), C.output⟩

lemma killGate_monotone2 (w0 : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (killGate w0 g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (killGate w0 g).inputs.length ≤ 2 := by
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hand | hor
  · unfold killGate
    rw [hand]
    split_ifs
    · simp
    · exact ⟨by simp [hand], hlen⟩
  · unfold killGate
    rw [hor]
    refine ⟨by simp, le_trans (List.length_filter_le _ _) hlen⟩

lemma killWire_monotone2 (w0 : ℕ) (C : Circuit) (hm : Monotone2 C) : Monotone2 (killWire w0 C) := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
  exact killGate_monotone2 w0 g0 (hm g0 hg0)

lemma killWire_gateAt (w0 : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt (killWire w0 C) k = killGate w0 (gateAt C k) := by
  unfold gateAt killWire
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
    Option.map_some, Option.getD_some]

lemma killGate_inputs_subset (w0 : ℕ) (g : Gate) (u : ℕ) (hu : u ∈ (killGate w0 g).inputs) :
    u ∈ g.inputs := by
  unfold killGate at hu
  cases h : g.op <;> simp only [h] at hu
  · split_ifs at hu
    · simp at hu
    · exact hu
  · exact (List.mem_filter.mp hu).1
  · exact hu
  · exact hu
  · exact hu

lemma killWire_readsBack (n w0 : ℕ) (C : Circuit) (hrb : ReadsBack n C) :
    ReadsBack n (killWire w0 C) := by
  intro j hj u hu
  have hj' : j < C.gates.length := by simpa [killWire] using hj
  rw [killWire_gateAt w0 C j hj'] at hu
  exact hrb j hj' u (killGate_inputs_subset w0 _ u hu)

lemma killGate_no_mem (w0 : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    w0 ∉ (killGate w0 g).inputs := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hand | hor
  · unfold killGate
    rw [hand]
    split_ifs with h
    · simp
    · exact h
  · unfold killGate
    rw [hor]
    simp

lemma killGate_and_imp (w0 : ℕ) (g : Gate) (h : (killGate w0 g).op = GateOp.and) :
    g.op = GateOp.and := by
  unfold killGate at h
  cases hop : g.op <;> simp only [hop] at h
  · rfl
  · cases h
  · cases h
  · cases h
  · cases h

lemma killWire_inCone_imp (n w0 : ℕ) (C : Circuit) {a b : ℕ}
    (h : InCone n (killWire w0 C) a b) : InCone n C a b := by
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    rw [inCone_iff] at h ⊢
    rcases h with ⟨hb, w, hw_in, hw_ge, hw_lt, ha⟩
    have hb' : b < C.gates.length := by simpa [killWire] using hb
    rw [killWire_gateAt w0 C b hb'] at hw_in
    refine ⟨hb', w, killGate_inputs_subset w0 _ w hw_in, hw_ge, hw_lt, ?_⟩
    rcases ha with rfl | hsub
    · exact Or.inl rfl
    · exact Or.inr (ih (w - n) (by omega) hsub)

lemma killWire_not_inCone (n i : ℕ) (C : Circuit) (hm : Monotone2 C) (m : ℕ) :
    ¬ InCone n (killWire (n + i) C) i m := by
  intro h
  obtain ⟨k, hk, _, _, hread⟩ := inCone_exists_reader n (killWire (n + i) C) h
  have hk' : k < C.gates.length := by simpa [killWire] using hk
  rw [killWire_gateAt (n + i) C k hk'] at hread
  have hmem : gateAt C k ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
    exact List.getElem_mem hk'
  exact killGate_no_mem (n + i) (gateAt C k) (hm _ hmem).1 hread

lemma killWire_wires_eq_of_false (n w0 : ℕ) (C : Circuit) (hm : Monotone2 C) (hrb : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (hf : (C.wires x).getD w0 false = false) :
    ∀ u : ℕ, ((killWire w0 C).wires x).getD u false = (C.wires x).getD u false := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    by_cases hlt : u < n
    · rw [wires_getD_lt _ x u (by omega), wires_getD_lt _ x u (by omega)]
    · by_cases hge : n + C.gates.length ≤ u
      · have h1 : ((killWire w0 C).wires x).length = n + C.gates.length := by
          rw [wires_length, hx]; simp [killWire]
        have h2 : (C.wires x).length = n + C.gates.length := by
          rw [wires_length, hx]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
            List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      · have hk : u - n < C.gates.length := by omega
        have heq : u = n + (u - n) := by omega
        rw [heq]
        rw [wires_getD_gate n (killWire w0 C) (killWire_readsBack n w0 C hrb) x hx (u - n) (by simpa [killWire] using hk)]
        rw [wires_getD_gate n C hrb x hx (u - n) hk]
        rw [killWire_gateAt w0 C (u - n) hk]
        have hmem : gateAt C (u - n) ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
          exact List.getElem_mem hk
        have hmap : ∀ l : List ℕ, (∀ v ∈ l, v < n + (u - n)) →
            l.map (fun i => ((killWire w0 C).wires x).getD i false) =
            l.map (fun i => (C.wires x).getD i false) := by
          intro l hl
          apply List.map_congr_left
          intro v hv
          exact ih v (by have := hl v hv; omega)
        have hrb_k : ∀ v ∈ (gateAt C (u - n)).inputs, v < n + (u - n) := hrb (u - n) hk
        have hop := (hm _ hmem).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hand | hor
        · unfold killGate
          rw [hand]
          split_ifs with hw0
          · simp only [GateOp.eval, List.map_nil, List.any_nil]
            symm
            rw [List.all_eq_false]
            exact ⟨false, List.mem_map.mpr ⟨w0, hw0, hf⟩, by decide⟩
          · dsimp only
            rw [hand]
            congr 1
            exact hmap _ hrb_k
        · unfold killGate
          rw [hor]
          dsimp only [GateOp.eval]
          rw [hmap _ (fun v hv => hrb_k v (List.mem_filter.mp hv).1)]
          rw [Bool.eq_iff_iff]
          simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
          constructor
          · rintro ⟨_, ⟨v, ⟨hv, _⟩, rfl⟩, htrue⟩
            exact ⟨_, ⟨v, hv, rfl⟩, htrue⟩
          · rintro ⟨_, ⟨v, hv, rfl⟩, htrue⟩
            have hne : v ≠ w0 := by
              intro hvw
              subst hvw
              rw [hf] at htrue
              cases htrue
            exact ⟨_, ⟨v, ⟨hv, hne⟩, rfl⟩, htrue⟩

lemma killWire_wires_eq_le (n i : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) :
    ∀ u ≤ n + i, ((killWire (n + i) C).wires x).getD u false = (C.wires x).getD u false := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hle
    by_cases hlt : u < n
    · rw [wires_getD_lt _ x u (by omega), wires_getD_lt _ x u (by omega)]
    · by_cases hge : n + C.gates.length ≤ u
      · have h1 : ((killWire (n + i) C).wires x).length = n + C.gates.length := by
          rw [wires_length, hx]; simp [killWire]
        have h2 : (C.wires x).length = n + C.gates.length := by
          rw [wires_length, hx]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
            List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      · have hk : u - n < C.gates.length := by omega
        have heq : u = n + (u - n) := by omega
        rw [heq]
        rw [wires_getD_gate n (killWire (n + i) C) (killWire_readsBack n (n + i) C hrb) x hx (u - n) (by simpa [killWire] using hk)]
        rw [wires_getD_gate n C hrb x hx (u - n) hk]
        rw [killWire_gateAt (n + i) C (u - n) hk]
        have hno : n + i ∉ (gateAt C (u - n)).inputs := by
          intro hmem
          have := hrb (u - n) hk (n + i) hmem
          omega
        have hkill_eq : killGate (n + i) (gateAt C (u - n)) = gateAt C (u - n) := by
          unfold killGate
          cases hop : (gateAt C (u - n)).op
          · simp [hno]
          · have hfilt : (gateAt C (u - n)).inputs.filter (fun v => decide (v ≠ n + i)) = (gateAt C (u - n)).inputs := by
              rw [List.filter_eq_self]
              intro v hv
              simp only [decide_eq_true_eq]
              intro hEq
              subst hEq
              exact hno hv
            cases g : gateAt C (u - n) with
            | mk op ins =>
              simp only [g] at hop hfilt ⊢
              subst hop
              exact congrArg (Gate.mk GateOp.or) hfilt
          · rfl
          · rfl
          · rfl
        rw [hkill_eq]
        congr 1
        apply List.map_congr_left
        intro v hv
        have hvlt := hrb (u - n) hk v hv
        exact ih v (by omega) (by omega)

def substShift (n k w u : ℕ) : ℕ :=
  if u = n + k then w else if n + k < u then u - 1 else u

def unShift (k m : ℕ) : ℕ :=
  if k ≤ m then m + 1 else m

def delGate (n k w : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (fun g => ⟨g.op, g.inputs.map (substShift n k w)⟩),
   substShift n k w C.output⟩

lemma delGate_length (n k w : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (delGate n k w C).gates.length = C.gates.length - 1 := by
  simp [delGate, List.length_eraseIdx, hk]

lemma delGate_monotone2 (n k w : ℕ) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (delGate n k w C) := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
  have hg0' : g0 ∈ C.gates := List.mem_of_mem_eraseIdx hg0
  rcases hm g0 hg0' with ⟨hop, hlen⟩
  exact ⟨hop, by simpa using hlen⟩

lemma delGate_gateAt (n k w : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (m : ℕ) (hm : m < C.gates.length - 1) :
    gateAt (delGate n k w C) m =
      ⟨(gateAt C (unShift k m)).op, (gateAt C (unShift k m)).inputs.map (substShift n k w)⟩ := by
  unfold gateAt delGate
  have hm_len : m < (C.gates.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt hk]; exact hm
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hm_len,
    Option.map_some, Option.getD_some]
  by_cases hmk : m < k
  · have hu : unShift k m = m := by unfold unShift; split_ifs <;> omega
    rw [hu, List.getElem_eraseIdx_of_lt hm_len hmk, List.getElem?_eq_getElem (by omega), Option.getD_some]
  · have hu : unShift k m = m + 1 := by unfold unShift; split_ifs <;> omega
    rw [hu, List.getElem_eraseIdx_of_ge hm_len (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some]

lemma delGate_readsBack (n k w : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (hk : k < C.gates.length) (hw : w < n + k) :
    ReadsBack n (delGate n k w C) := by
  intro m hm u hu
  have hm' : m < C.gates.length - 1 := by rwa [delGate_length n k w C hk] at hm
  rw [delGate_gateAt n k w C hk m hm'] at hu
  rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
  have hvlt : v < n + unShift k m := hrb (unShift k m) (by unfold unShift; split_ifs <;> omega) v hv
  unfold substShift unShift at *
  split_ifs at * <;> omega

lemma delGate_inCone_imp (n k w : ℕ) (C : Circuit) (hrb : ReadsBack n C) (hk : k < C.gates.length) (hw : w < n + k)
    (hw_ok : n ≤ w → (w - n) ∈ (gateAt C k).inputs.map (· - n) ∧ w ∈ (gateAt C k).inputs ∨ ∀ m < C.gates.length, n + k ∉ (gateAt C m).inputs) :
    ∀ a b : ℕ, InCone n (delGate n k w C) a b → InCone n C (unShift k a) (unShift k b) := by
  intro a b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro h
    rw [inCone_iff] at h
    rcases h with ⟨hb, u, hu_in, hu_ge, hu_lt, ha⟩
    have hb' : b < C.gates.length - 1 := by rwa [delGate_length n k w C hk] at hb
    rw [delGate_gateAt n k w C hk b hb'] at hu_in
    rcases List.mem_map.mp hu_in with ⟨v, hv_in, rfl⟩
    have hub_lt : unShift k b < C.gates.length := by unfold unShift; split_ifs <;> omega
    by_cases hvk : v = n + k
    · subst hvk
      simp only [substShift, ite_true] at hu_ge hu_lt ha
      rcases hw_ok hu_ge with ⟨_, hw_mem⟩ | hnoread
      · have hkb : k < unShift k b := by
          have hv_lt := hrb (unShift k b) hub_lt (n + k) hv_in
          omega
        have hkb_cone : InCone n C k (unShift k b) := by
          rw [inCone_iff]
          exact ⟨hub_lt, n + k, hv_in, by omega, by omega, Or.inl (by omega)⟩
        have hwk_cone : InCone n C (w - n) k := by
          rw [inCone_iff]
          exact ⟨hk, w, hw_mem, hu_ge, hw, Or.inl rfl⟩
        have hwb_cone : InCone n C (w - n) (unShift k b) := inCone_trans n C hwk_cone hkb_cone
        have hun : unShift k (w - n) = w - n := by unfold unShift; split_ifs <;> omega
        rcases ha with rfl | hsub
        · rwa [hun]
        · have hrec := ih (w - n) (by omega) hsub
          rw [hun] at hrec
          exact inCone_trans n C hrec hwb_cone
      · exact absurd hv_in (hnoread (unShift k b) hub_lt)
    · have hu_eq : substShift n k w v = if n + k < v then v - 1 else v := by
        unfold substShift; simp [hvk]
      rw [hu_eq] at hu_ge hu_lt ha
      have hvn : n ≤ v := by split_ifs at hu_ge <;> omega
      have hv_ub : v < n + unShift k b := by
        unfold unShift
        split_ifs at hu_lt ⊢ <;> omega
      have hun_v : unShift k ((if n + k < v then v - 1 else v) - n) = v - n := by
        unfold unShift
        split_ifs at hu_ge ⊢ <;> omega
      rcases ha with rfl | hsub
      · rw [hun_v, inCone_iff]
        exact ⟨hub_lt, v, hv_in, hvn, hv_ub, Or.inl rfl⟩
      · have hrec := ih ((if n + k < v then v - 1 else v) - n) (by omega) hsub
        rw [hun_v] at hrec
        rw [inCone_iff]
        exact ⟨hub_lt, v, hv_in, hvn, hv_ub, Or.inr hrec⟩

lemma delGate_wires_eq (n k w : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (hk : k < C.gates.length) (hw : w < n + k) (x : List Bool) (hx : x.length = n)
    (heq_k : (C.wires x).getD (n + k) false = (C.wires x).getD w false ∨
      ∀ m < C.gates.length, n + k ∉ (gateAt C m).inputs) :
    ∀ u < n + (C.gates.length - 1),
      ((delGate n k w C).wires x).getD u false =
        (C.wires x).getD (if n + k ≤ u then u + 1 else u) false := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    by_cases hlt : u < n
    · have hnot : ¬ n + k ≤ u := by omega
      simp only [hnot, ite_false]
      rw [wires_getD_lt _ x u (by omega), wires_getD_lt _ x u (by omega)]
    · have hm : u - n < C.gates.length - 1 := by omega
      have hu_eq : u = n + (u - n) := by omega
      have hidx : (if n + k ≤ u then u + 1 else u) = n + unShift k (u - n) := by
        unfold unShift; split_ifs <;> omega
      rw [hidx]
      conv_lhs => rw [hu_eq]
      rw [wires_getD_gate n (delGate n k w C) (delGate_readsBack n k w C hrb hk hw) x hx (u - n)
        (by rw [delGate_length n k w C hk]; exact hm)]
      rw [delGate_gateAt n k w C hk (u - n) hm]
      have hub_lt : unShift k (u - n) < C.gates.length := by unfold unShift; split_ifs <;> omega
      rw [wires_getD_gate n C hrb x hx (unShift k (u - n)) hub_lt]
      dsimp only
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro v hv
      simp only [Function.comp_apply]
      have hv_lt : v < n + unShift k (u - n) := hrb (unShift k (u - n)) hub_lt v hv
      by_cases hvk : v = n + k
      · subst hvk
        rcases heq_k with hkval | hnoread
        · simp only [substShift, ite_true]
          rw [ih w (by unfold unShift at hv_lt; split_ifs at hv_lt <;> omega) (by omega)]
          have hnot : ¬ n + k ≤ w := by omega
          simp only [hnot, ite_false, hkval]
        · exact absurd hv (hnoread (unShift k (u - n)) hub_lt)
      · have hsub_lt : substShift n k w v < u := by
          unfold substShift; unfold unShift at hv_lt; split_ifs at hv_lt ⊢ <;> omega
        rw [ih (substShift n k w v) hsub_lt (by omega)]
        congr 1
        unfold substShift
        split_ifs <;> omega

lemma append_or_inCone_iff (n : ℕ) (C : Circuit) (a b x y : ℕ)
    (hy : y < C.gates.length) :
    InCone n ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩ x y ↔ InCone n C x y := by
  unfold InCone cones
  rw [List.foldl_append, foldl_coneStep_getD_lt n _ _ y (by rw [foldl_coneStep_length, List.length_nil, zero_add]; exact hy)]

lemma append_or_wires_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : List Bool) (hx : x.length = n)
    (u : ℕ) (hu : u < n + C.gates.length) :
    ((Circuit.mk (C.gates ++ [⟨GateOp.or, [a, b]⟩]) (n + C.gates.length)).wires x).getD u false =
      (C.wires x).getD u false := by
  unfold Circuit.wires
  change ((C.gates ++ [Gate.mk GateOp.or [a, b]]).foldl stepWire x).getD u false =
    (C.gates.foldl stepWire x).getD u false
  rw [List.foldl_append]
  have hlen : (C.gates.foldl stepWire x).length = n + C.gates.length := by
    rw [foldl_stepWire_length, hx]
  exact foldl_stepWire_getD_lt _ _ u (by omega)

lemma append_or_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : List Bool) (hx : x.length = n) :
    (Circuit.mk (C.gates ++ [⟨GateOp.or, [a, b]⟩]) (n + C.gates.length)).eval x =
      ((C.wires x).getD a false || (C.wires x).getD b false) := by
  unfold Circuit.eval Circuit.wires
  change ((C.gates ++ [Gate.mk GateOp.or [a, b]]).foldl stepWire x).getD (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (C.gates.foldl stepWire x).length = n + C.gates.length := by
    rw [foldl_stepWire_length, hx]
  simp only [stepWire, List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, GateOp.eval, List.map_cons,
    List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
  rfl

lemma andPairs_lt_of_embed (n : ℕ) (C C' : Circuit) (f : ℕ → ℕ)
    (hf_inj : Function.Injective f)
    (hf_lt : ∀ m < C'.gates.length, (gateAt C' m).op = GateOp.and → f m < C.gates.length)
    (hf_and : ∀ m < C'.gates.length, (gateAt C' m).op = GateOp.and → (gateAt C (f m)).op = GateOp.and)
    (hf_cone : ∀ a b, a < C'.gates.length → b < C'.gates.length →
      (gateAt C' a).op = GateOp.and → (gateAt C' b).op = GateOp.and →
      InCone n C' a b → InCone n C (f a) (f b))
    (i j : ℕ) (hi_lt : i < C.gates.length) (hj_lt : j < C.gates.length)
    (hi_and : (gateAt C i).op = GateOp.and) (hj_and : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    (hmiss : ∀ a b, a < C'.gates.length → b < C'.gates.length →
      (gateAt C' a).op = GateOp.and → (gateAt C' b).op = GateOp.and →
      InCone n C' a b → f a ≠ i) :
    andPairs n C' < andPairs n C := by
  unfold andPairs
  let g : ℕ × ℕ → ℕ × ℕ := fun p => (f p.1, f p.2)
  have hg_inj : Function.Injective g := fun p q h =>
    Prod.ext (hf_inj (congrArg Prod.fst h)) (hf_inj (congrArg Prod.snd h))
  refine lt_of_eq_of_lt (Finset.card_image_of_injective _ hg_inj).symm (Finset.card_lt_card ?_)
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hi_lt, hj_lt⟩, hi_and, hj_and, hij⟩
    · intro hmem
      rcases Finset.mem_image.mp hmem with ⟨⟨a, b⟩, hab, hEq⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
      have hfa : f a = i := congrArg Prod.fst hEq
      exact hmiss a b hab.1.1 hab.1.2 hab.2.1 hab.2.2.1 hab.2.2.2 hfa
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨⟨a, b⟩, hab, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab ⊢
    exact ⟨⟨hf_lt a hab.1.1 hab.2.1, hf_lt b hab.1.2 hab.2.2.1⟩,
      hf_and a hab.1.1 hab.2.1, hf_and b hab.1.2 hab.2.2.1,
      hf_cone a b hab.1.1 hab.1.2 hab.2.1 hab.2.2.1 hab.2.2.2⟩

end PEqualNP.Outside.L_meta_5160

set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.L_meta_5160 : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x5 x6 ∧ ∀ (x7 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x7 → (x3.wires (x1 x7)).getD ((26 : ℕ) + x5) Bool.false = Bool.false) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 ∧ (x6.size < x3.size ∨ x6.size = x3.size ∧ PEqualNP.TopForm.andPairs (26 : ℕ) x6 < PEqualNP.TopForm.andPairs (26 : ℕ) x3) := by
  dsimp only
  intro C hC hex
  rcases hC with ⟨hm, hrb, hpos, hneg⟩
  rcases hex with ⟨i, j, hi_and, hj_and, hij, hi_quad⟩
  have ⟨hij_lt, hj_lt⟩ := PEqualNP.Outside.L_meta_5160.inCone_lt 26 C hij
  have hi_lt : i < C.gates.length := by omega
  obtain ⟨k, hk_lt, hik, hkj, hk_read⟩ := PEqualNP.Outside.L_meta_5160.inCone_exists_reader 26 C hij
  have h00 : (0 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have hout_lt : C.output < 26 + C.gates.length := by
    by_contra hge
    have htrue := hpos 0 0 h00
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval at htrue
    have hlen : (C.wires ((List.ofFn fun (x6 : Fin 13) => decide (x6 = 0)) ++
        List.ofFn fun (x6 : Fin 13) => decide (x6 = 0))).length = 26 + C.gates.length := by
      rw [PEqualNP.Outside.L_meta_5160.wires_length]
      simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none] at htrue
    cases htrue
  let C1 := PEqualNP.Outside.L_meta_5160.killWire (26 + i) C
  have hC1_len : C1.gates.length = C.gates.length := by simp [C1, PEqualNP.Outside.L_meta_5160.killWire]
  have hC1_m : PEqualNP.MetaComplexity.Monotone2 C1 :=
    PEqualNP.Outside.L_meta_5160.killWire_monotone2 (26 + i) C hm
  have hC1_rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C1 :=
    PEqualNP.Outside.L_meta_5160.killWire_readsBack 26 (26 + i) C hrb
  have hk_C1 : (PEqualNP.MetaComplexity.NestedCover.gateAt C1 k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C1 k).inputs.length ≤ 1 := by
    rw [PEqualNP.Outside.L_meta_5160.killWire_gateAt (26 + i) C k hk_lt]
    have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt, Option.getD_some]
      exact List.getElem_mem hk_lt
    rcases hm _ hmem with ⟨hop, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hand | hor
    · unfold PEqualNP.Outside.L_meta_5160.killGate
      rw [hand]
      simp [hk_read]
    · unfold PEqualNP.Outside.L_meta_5160.killGate
      rw [hor]
      refine ⟨rfl, ?_⟩
      have hsub : ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.filter
          (fun u => decide (u ≠ 26 + i))).length < (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.length := by
        apply List.length_filter_lt_length_iff_exists.mpr
        exact ⟨26 + i, hk_read, by simp⟩
      dsimp only
      omega
  have hpair_len : ∀ p l : Fin 13, ((List.ofFn fun (x6 : Fin 13) => decide (x6 = p)) ++
      List.ofFn fun (x6 : Fin 13) => decide (x6 = l)).length = 26 := by
    intro p l; simp
  have hquad_len : ∀ Q : Finset (Fin 13),
      ((List.ofFn fun (x2 : Fin 13) => decide (x2 ∈ Q)) ++
        List.ofFn fun (x2 : Fin 13) => decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)).length = 26 := by
    intro Q; simp
  rcases hkins : (PEqualNP.MetaComplexity.NestedCover.gateAt C1 k).inputs with _ | ⟨w, rest⟩
  · -- Case A: gate k in C1 is `or []` (constant false)
    let C2 := PEqualNP.Outside.L_meta_5160.killWire (26 + k) C1
    have hC2_len : C2.gates.length = C.gates.length := by
      simp [C2, C1, PEqualNP.Outside.L_meta_5160.killWire]
    have hC2_m : PEqualNP.MetaComplexity.Monotone2 C2 :=
      PEqualNP.Outside.L_meta_5160.killWire_monotone2 (26 + k) C1 hC1_m
    have hC2_rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C2 :=
      PEqualNP.Outside.L_meta_5160.killWire_readsBack 26 (26 + k) C1 hC1_rb
    have hC1_k_false : ∀ x : List Bool, x.length = 26 → (C1.wires x).getD (26 + k) false = false := by
      intro x hx
      rw [PEqualNP.Outside.L_meta_5160.wires_getD_gate 26 C1 hC1_rb x hx k (by omega), hk_C1.1, hkins]
      rfl
    have hC2_wires : ∀ x : List Bool, x.length = 26 → ∀ u, (C2.wires x).getD u false = (C1.wires x).getD u false :=
      fun x hx => PEqualNP.Outside.L_meta_5160.killWire_wires_eq_of_false 26 (26 + k) C1 hC1_m hC1_rb x hx (hC1_k_false x hx)
    have hC2_noread : ∀ m < C2.gates.length, 26 + k ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C2 m).inputs := by
      intro m hm2
      have hm1 : m < C1.gates.length := by omega
      rw [PEqualNP.Outside.L_meta_5160.killWire_gateAt (26 + k) C1 m hm1]
      have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C1 m ∈ C1.gates := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm1, Option.getD_some]
        exact List.getElem_mem hm1
      exact PEqualNP.Outside.L_meta_5160.killGate_no_mem (26 + k) _ (hC1_m _ hmem).1
    let C3 := PEqualNP.Outside.L_meta_5160.delGate 26 k 0 C2
    have hC3_len : C3.gates.length = C.gates.length - 1 := by
      rw [PEqualNP.Outside.L_meta_5160.delGate_length 26 k 0 C2 (by omega), hC2_len]
    have hC3_m : PEqualNP.MetaComplexity.Monotone2 C3 :=
      PEqualNP.Outside.L_meta_5160.delGate_monotone2 26 k 0 C2 hC2_m
    have hC3_rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C3 :=
      PEqualNP.Outside.L_meta_5160.delGate_readsBack 26 k 0 C2 hC2_rb (by omega) (by omega)
    have hC3_wires : ∀ x : List Bool, x.length = 26 → ∀ u < 26 + (C.gates.length - 1),
        (C3.wires x).getD u false = (C1.wires x).getD (if 26 + k ≤ u then u + 1 else u) false := by
      intro x hx u hu
      rw [PEqualNP.Outside.L_meta_5160.delGate_wires_eq 26 k 0 C2 hC2_rb (by omega) (by omega) x hx (Or.inr hC2_noread) u (by omega)]
      exact hC2_wires x hx _
    by_cases hout_k : C.output = 26 + k
    · -- C.output = 26 + k: just output 26 + i! Size strictly decreases!
      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C3.gates, 26 + i⟩
      refine ⟨C', ⟨hC3_m, hC3_rb, ?_, ?_⟩, Or.inl (by change C3.gates.length < C.gates.length; omega)⟩
      · intro p l hpl
        let x := (List.ofFn fun (x6 : Fin 13) => decide (x6 = p)) ++
          List.ofFn fun (x6 : Fin 13) => decide (x6 = l)
        have hx : x.length = 26 := hpair_len p l
        change (C3.wires x).getD (26 + i) false = true
        rw [hC3_wires x hx (26 + i) (by omega)]
        have hnot : ¬ 26 + k ≤ 26 + i := by omega
        simp only [hnot, ite_false]
        rw [PEqualNP.Outside.L_meta_5160.killWire_wires_eq_le 26 i C hrb x hx (26 + i) (le_refl _)]
        by_contra hne
        have hf : (C.wires x).getD (26 + i) false = false := by
          cases h : (C.wires x).getD (26 + i) false
          · rfl
          · exact (hne h).elim
        have hev := hpos p l hpl
        change (C.wires x).getD C.output false = true at hev
        rw [hout_k] at hev
        have h1 := PEqualNP.Outside.L_meta_5160.killWire_wires_eq_of_false 26 (26 + i) C hm hrb x hx hf (26 + k)
        rw [hC1_k_false x hx] at h1
        rw [← h1] at hev
        cases hev
      · intro Q hQ
        let x := (List.ofFn fun (x2 : Fin 13) => decide (x2 ∈ Q)) ++
          List.ofFn fun (x2 : Fin 13) => decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)
        have hx : x.length = 26 := hquad_len Q
        change (C3.wires x).getD (26 + i) false = false
        rw [hC3_wires x hx (26 + i) (by omega)]
        have hnot : ¬ 26 + k ≤ 26 + i := by omega
        simp only [hnot, ite_false]
        rw [PEqualNP.Outside.L_meta_5160.killWire_wires_eq_le 26 i C hrb x hx (26 + i) (le_refl _)]
        exact hi_quad Q hQ
    · -- C.output ≠ 26 + k: append OR [substShift C.output, 26 + i]
      let out3 := PEqualNP.Outside.L_meta_5160.substShift 26 k 0 C.output
      have hout3_lt : out3 < 26 + C3.gates.length := by
        unfold out3 PEqualNP.Outside.L_meta_5160.substShift
        split_ifs <;> omega
      let C' : PEqualNP.CircuitLowerBounds.Circuit :=
        ⟨C3.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [out3, 26 + i]⟩], 26 + C3.gates.length⟩
      have hC'_len : C'.gates.length = C.gates.length := by
        simp [C', hC3_len]; omega
      have hC'_m : PEqualNP.MetaComplexity.Monotone2 C' := by
        intro g hg
        simp only [C', List.mem_append, List.mem_singleton] at hg
        rcases hg with hg3 | rfl
        · exact hC3_m g hg3
        · simp
      have hC'_rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' := by
        intro m hm u hu
        by_cases hm3 : m < C3.gates.length
        · have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C' m =
              PEqualNP.MetaComplexity.NestedCover.gateAt C3 m := by
            unfold PEqualNP.MetaComplexity.NestedCover.gateAt
            simp only [C', List.getD_eq_getElem?_getD, List.getElem?_append_left hm3]
          rw [hgat] at hu
          exact hC3_rb m hm3 u hu
        · have hmeq : m = C3.gates.length := by simp [C'] at hm; omega
          subst hmeq
          have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C' C3.gates.length =
              ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [out3, 26 + i]⟩ := by
            unfold PEqualNP.MetaComplexity.NestedCover.gateAt
            simp only [C', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [hgat] at hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · exact hout3_lt
          · omega
      have hC'_eval : ∀ x : List Bool, x.length = 26 →
          C'.eval x = ((C1.wires x).getD C.output false || (C.wires x).getD (26 + i) false) := by
        intro x hx
        rw [PEqualNP.Outside.L_meta_5160.append_or_eval 26 C3 out3 (26 + i) x hx]
        rw [hC3_wires x hx out3 (by omega), hC3_wires x hx (26 + i) (by omega)]
        have h1 : (if 26 + k ≤ out3 then out3 + 1 else out3) = C.output := by
          unfold out3 PEqualNP.Outside.L_meta_5160.substShift
          split_ifs <;> omega
        have h2 : ¬ 26 + k ≤ 26 + i := by omega
        simp only [h1, h2, ite_false]
        rw [PEqualNP.Outside.L_meta_5160.killWire_wires_eq_le 26 i C hrb x hx (26 + i) (le_refl _)]
      refine ⟨C', ⟨hC'_m, hC'_rb, ?_, ?_⟩, Or.inr ⟨hC'_len, ?_⟩⟩
      · intro p l hpl
        let x := (List.ofFn fun (x6 : Fin 13) => decide (x6 = p)) ++
          List.ofFn fun (x6 : Fin 13) => decide (x6 = l)
        have hx : x.length = 26 := hpair_len p l
        rw [hC'_eval x hx]
        cases hi_v : (C.wires x).getD (26 + i) false
        · rw [PEqualNP.Outside.L_meta_5160.killWire_wires_eq_of_false 26 (26 + i) C hm hrb x hx hi_v C.output]
          have hev := hpos p l hpl
          change (C.wires x).getD C.output false = true at hev
          rw [hev]; rfl
        · simp
      · intro Q hQ
        let x := (List.ofFn fun (x2 : Fin 13) => decide (x2 ∈ Q)) ++
          List.ofFn fun (x2 : Fin 13) => decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)
        have hx : x.length = 26 := hquad_len Q
        rw [hC'_eval x hx, hi_quad Q hQ]
        rw [PEqualNP.Outside.L_meta_5160.killWire_wires_eq_of_false 26 (26 + i) C hm hrb x hx (hi_quad Q hQ) C.output]
        have hev := hneg Q hQ
        change (C.wires x).getD C.output false = false at hev
        rw [hev]; rfl
      · have hnot_last : ∀ m < C'.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C' m).op = PEqualNP.CircuitLowerBounds.GateOp.and → m < C3.gates.length := by
          intro m hm' hand
          by_contra hge
          have hmeq : m = C3.gates.length := by omega
          subst hmeq
          have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C' C3.gates.length =
              ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [out3, 26 + i]⟩ := by
            unfold PEqualNP.MetaComplexity.NestedCover.gateAt
            simp only [C', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [hgat] at hand
          cases hand
        have hgat3 : ∀ m < C3.gates.length,
            PEqualNP.MetaComplexity.NestedCover.gateAt C' m =
              PEqualNP.MetaComplexity.NestedCover.gateAt C3 m := by
          intro m hm3
          unfold PEqualNP.MetaComplexity.NestedCover.gateAt
          simp only [C', List.getD_eq_getElem?_getD, List.getElem?_append_left hm3]
        apply PEqualNP.Outside.L_meta_5160.andPairs_lt_of_embed 26 C C' (PEqualNP.Outside.L_meta_5160.unShift k)
        · intro a b hab; unfold PEqualNP.Outside.L_meta_5160.unShift at hab; split_ifs at hab <;> omega
        · intro m hm' hand
          have hm3 := hnot_last m hm' hand
          unfold PEqualNP.Outside.L_meta_5160.unShift; split_ifs <;> omega
        · intro m hm' hand
          have hm3 := hnot_last m hm' hand
          rw [hgat3 m hm3, PEqualNP.Outside.L_meta_5160.delGate_gateAt 26 k 0 C2 (by omega) m (by omega)] at hand
          dsimp only at hand
          rw [PEqualNP.Outside.L_meta_5160.killWire_gateAt (26 + k) C1 _ (by unfold PEqualNP.Outside.L_meta_5160.unShift; split_ifs <;> omega)] at hand
          have h1 := PEqualNP.Outside.L_meta_5160.killGate_and_imp (26 + k) _ hand
          rw [PEqualNP.Outside.L_meta_5160.killWire_gateAt (26 + i) C _ (by unfold PEqualNP.Outside.L_meta_5160.unShift; split_ifs <;> omega)] at h1
          exact PEqualNP.Outside.L_meta_5160.killGate_and_imp (26 + i) _ h1
        · intro a b _ hb' _ hb_and hab
          have hb3 := hnot_last b hb' hb_and
          rw [PEqualNP.Outside.L_meta_5160.append_or_inCone_iff 26 C3 out3 (26 + i) a b hb3] at hab
          have h2 := PEqualNP.Outside.L_meta_5160.delGate_inCone_imp 26 k 0 C2 hC2_rb (by omega) (by omega) (fun _ => Or.inr hC2_noread) a b hab
          have h1 := PEqualNP.Outside.L_meta_5160.killWire_inCone_imp 26 (26 + k) C1 h2
          exact PEqualNP.Outside.L_meta_5160.killWire_inCone_imp 26 (26 + i) C h1
        · exact hi_lt
        · exact hj_lt
        · exact hi_and
        · exact hj_and
        · exact hij
        · intro a b _ hb' _ hb_and hab hfa
          have hb3 := hnot_last b hb' hb_and
          rw [PEqualNP.Outside.L_meta_5160.append_or_inCone_iff 26 C3 out3 (26 + i) a b hb3] at hab
          have h2 := PEqualNP.Outside.L_meta_5160.delGate_inCone_imp 26 k 0 C2 hC2_rb (by omega) (by omega) (fun _ => Or.inr hC2_noread) a b hab
          have h1 := PEqualNP.Outside.L_meta_5160.killWire_inCone_imp 26 (26 + k) C1 h2
          rw [hfa] at h1
          exact PEqualNP.Outside.L_meta_5160.killWire_not_inCone 26 i C hm _ h1
  · -- Case B: gate k in C1 is `or [w]` (since length ≤ 1, rest = [])
    have hrest : rest = [] := by
      have hlen := hk_C1.2
      rw [hkins] at hlen
      cases rest with
      | nil => rfl
      | cons _ _ => simp at hlen
    subst hrest
    have hw_lt : w < 26 + k := hC1_rb k (by omega) w (by rw [hkins]; simp)
    have hC1_k_eq : ∀ x : List Bool, x.length = 26 → (C1.wires x).getD (26 + k) false = (C1.wires x).getD w false := by
      intro x hx
      rw [PEqualNP.Outside.L_meta_5160.wires_getD_gate 26 C1 hC1_rb x hx k (by omega), hk_C1.1, hkins]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    let C3 := PEqualNP.Outside.L_meta_5160.delGate 26 k w C1
    have hC3_len : C3.gates.length = C.gates.length - 1 := by
      rw [PEqualNP.Outside.L_meta_5160.delGate_length 26 k w C1 (by omega), hC1_len]
    have hC3_m : PEqualNP.MetaComplexity.Monotone2 C3 :=
      PEqualNP.Outside.L_meta_5160.delGate_monotone2 26 k w C1 hC1_m
    have hC3_rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C3 :=
      PEqualNP.Outside.L_meta_5160.delGate_readsBack 26 k w C1 hC1_rb (by omega) hw_lt
    have hC3_wires : ∀ x : List Bool, x.length = 26 → ∀ u < 26 + (C.gates.length - 1),
        (C3.wires x).getD u false = (C1.wires x).getD (if 26 + k ≤ u then u + 1 else u) false :=
      fun x hx u hu => PEqualNP.Outside.L_meta_5160.delGate_wires_eq 26 k w C1 hC1_rb (by omega) hw_lt x hx (Or.inl (hC1_k_eq x hx)) u (by omega)
    let out3 := PEqualNP.Outside.L_meta_5160.substShift 26 k w C.output
    have hout3_lt : out3 < 26 + C3.gates.length := by
      unfold out3 PEqualNP.Outside.L_meta_5160.substShift
      split_ifs <;> omega
    let C' : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨C3.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [out3, 26 + i]⟩], 26 + C3.gates.length⟩
    have hC'_len : C'.gates.length = C.gates.length := by
      simp [C', hC3_len]; omega
    have hC'_m : PEqualNP.MetaComplexity.Monotone2 C' := by
      intro g hg
      simp only [C', List.mem_append, List.mem_singleton] at hg
      rcases hg with hg3 | rfl
      · exact hC3_m g hg3
      · simp
    have hC'_rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' := by
      intro m hm u hu
      by_cases hm3 : m < C3.gates.length
      · have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C' m =
            PEqualNP.MetaComplexity.NestedCover.gateAt C3 m := by
          unfold PEqualNP.MetaComplexity.NestedCover.gateAt
          simp only [C', List.getD_eq_getElem?_getD, List.getElem?_append_left hm3]
        rw [hgat] at hu
        exact hC3_rb m hm3 u hu
      · have hmeq : m = C3.gates.length := by simp [C'] at hm; omega
        subst hmeq
        have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C' C3.gates.length =
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [out3, 26 + i]⟩ := by
          unfold PEqualNP.MetaComplexity.NestedCover.gateAt
          simp only [C', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [hgat] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact hout3_lt
        · omega
    have hC'_eval : ∀ x : List Bool, x.length = 26 →
        C'.eval x = ((C1.wires x).getD C.output false || (C.wires x).getD (26 + i) false) := by
      intro x hx
      rw [PEqualNP.Outside.L_meta_5160.append_or_eval 26 C3 out3 (26 + i) x hx]
      rw [hC3_wires x hx out3 (by omega), hC3_wires x hx (26 + i) (by omega)]
      have h2 : ¬ 26 + k ≤ 26 + i := by omega
      simp only [h2, ite_false]
      rw [PEqualNP.Outside.L_meta_5160.killWire_wires_eq_le 26 i C hrb x hx (26 + i) (le_refl _)]
      congr 1
      by_cases hok : C.output = 26 + k
      · rw [hok]
        have ho3 : out3 = w := by unfold out3 PEqualNP.Outside.L_meta_5160.substShift; simp [hok]
        rw [ho3]
        have hnw : ¬ 26 + k ≤ w := by omega
        simp only [hnw, ite_false, hC1_k_eq x hx]
      · have h1 : (if 26 + k ≤ out3 then out3 + 1 else out3) = C.output := by
          unfold out3 PEqualNP.Outside.L_meta_5160.substShift
          split_ifs <;> omega
        rw [h1]
    refine ⟨C', ⟨hC'_m, hC'_rb, ?_, ?_⟩, Or.inr ⟨hC'_len, ?_⟩⟩
    · intro p l hpl
      let x := (List.ofFn fun (x6 : Fin 13) => decide (x6 = p)) ++
        List.ofFn fun (x6 : Fin 13) => decide (x6 = l)
      have hx : x.length = 26 := hpair_len p l
      rw [hC'_eval x hx]
      cases hi_v : (C.wires x).getD (26 + i) false
      · rw [PEqualNP.Outside.L_meta_5160.killWire_wires_eq_of_false 26 (26 + i) C hm hrb x hx hi_v C.output]
        have hev := hpos p l hpl
        change (C.wires x).getD C.output false = true at hev
        rw [hev]; rfl
      · simp
    · intro Q hQ
      let x := (List.ofFn fun (x2 : Fin 13) => decide (x2 ∈ Q)) ++
        List.ofFn fun (x2 : Fin 13) => decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)
      have hx : x.length = 26 := hquad_len Q
      rw [hC'_eval x hx, hi_quad Q hQ]
      rw [PEqualNP.Outside.L_meta_5160.killWire_wires_eq_of_false 26 (26 + i) C hm hrb x hx (hi_quad Q hQ) C.output]
      have hev := hneg Q hQ
      change (C.wires x).getD C.output false = false at hev
      rw [hev]; rfl
    · have hnot_last : ∀ m < C'.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C' m).op = PEqualNP.CircuitLowerBounds.GateOp.and → m < C3.gates.length := by
        intro m hm' hand
        by_contra hge
        have hmeq : m = C3.gates.length := by omega
        subst hmeq
        have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C' C3.gates.length =
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [out3, 26 + i]⟩ := by
          unfold PEqualNP.MetaComplexity.NestedCover.gateAt
          simp only [C', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [hgat] at hand
        cases hand
      have hgat3 : ∀ m < C3.gates.length,
          PEqualNP.MetaComplexity.NestedCover.gateAt C' m =
            PEqualNP.MetaComplexity.NestedCover.gateAt C3 m := by
        intro m hm3
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        simp only [C', List.getD_eq_getElem?_getD, List.getElem?_append_left hm3]
      have hw_ok : 26 ≤ w → (w - 26) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C1 k).inputs.map (· - 26) ∧
          w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C1 k).inputs ∨
          ∀ m < C1.gates.length, 26 + k ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C1 m).inputs := by
        intro _; exact Or.inl ⟨by rw [hkins]; simp, by rw [hkins]; simp⟩
      apply PEqualNP.Outside.L_meta_5160.andPairs_lt_of_embed 26 C C' (PEqualNP.Outside.L_meta_5160.unShift k)
      · intro a b hab; unfold PEqualNP.Outside.L_meta_5160.unShift at hab; split_ifs at hab <;> omega
      · intro m hm' hand
        have hm3 := hnot_last m hm' hand
        unfold PEqualNP.Outside.L_meta_5160.unShift; split_ifs <;> omega
      · intro m hm' hand
        have hm3 := hnot_last m hm' hand
        rw [hgat3 m hm3, PEqualNP.Outside.L_meta_5160.delGate_gateAt 26 k w C1 (by omega) m (by omega)] at hand
        dsimp only at hand
        rw [PEqualNP.Outside.L_meta_5160.killWire_gateAt (26 + i) C _ (by unfold PEqualNP.Outside.L_meta_5160.unShift; split_ifs <;> omega)] at hand
        exact PEqualNP.Outside.L_meta_5160.killGate_and_imp (26 + i) _ hand
      · intro a b _ hb' _ hb_and hab
        have hb3 := hnot_last b hb' hb_and
        rw [PEqualNP.Outside.L_meta_5160.append_or_inCone_iff 26 C3 out3 (26 + i) a b hb3] at hab
        have h1 := PEqualNP.Outside.L_meta_5160.delGate_inCone_imp 26 k w C1 hC1_rb (by omega) hw_lt hw_ok a b hab
        exact PEqualNP.Outside.L_meta_5160.killWire_inCone_imp 26 (26 + i) C h1
      · exact hi_lt
      · exact hj_lt
      · exact hi_and
      · exact hj_and
      · exact hij
      · intro a b _ hb' _ hb_and hab hfa
        have hb3 := hnot_last b hb' hb_and
        rw [PEqualNP.Outside.L_meta_5160.append_or_inCone_iff 26 C3 out3 (26 + i) a b hb3] at hab
        have h1 := PEqualNP.Outside.L_meta_5160.delGate_inCone_imp 26 k w C1 hC1_rb (by omega) hw_lt hw_ok a b hab
        rw [hfa] at h1
        exact PEqualNP.Outside.L_meta_5160.killWire_not_inCone 26 i C hm _ h1
