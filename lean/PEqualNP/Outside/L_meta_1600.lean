import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1600

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    wireVal n C p x = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp


lemma gateVal_eq {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    gateVal n C j x = (gateAt C j).op.eval ((gateAt C j).inputs.map fun r =>
      if r < n + j then wireVal n C r x else false) := by
  have hga : gateAt C j = C.gates[j] := by
    unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
  rw [hga]
  set w := n + j with hwdef
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, hwdef]
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then wireVal n C r x else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then wireVal n C r x else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    wireVal n C (n + j) x = gateVal n C j x := rfl

def foldS (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) : List (List ℕ) :=
  gs.foldl (fun cs g => cs ++ [F cs g]) []

lemma foldl_len (F : List (List ℕ) → Gate → List ℕ) (hs : List Gate) :
    ∀ cs : List (List ℕ), (hs.foldl (fun cs g => cs ++ [F cs g]) cs).length = cs.length + hs.length := by
  induction hs with
  | nil => intro cs; simp
  | cons h hs ih => intro cs; simp only [List.foldl_cons]; rw [ih]; simp; omega

lemma foldl_prefix (F : List (List ℕ) → Gate → List ℕ) (hs : List Gate) :
    ∀ (cs : List (List ℕ)) (i : ℕ), i < cs.length →
      (hs.foldl (fun cs g => cs ++ [F cs g]) cs).getD i [] = cs.getD i [] := by
  induction hs with
  | nil => intro cs i _; rfl
  | cons h hs ih =>
    intro cs i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]

lemma foldS_length (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) :
    (foldS F gs).length = gs.length := by
  unfold foldS; rw [foldl_len]; simp

lemma foldS_split (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) (j : ℕ) :
    foldS F gs = (gs.drop j).foldl (fun cs g => cs ++ [F cs g]) (foldS F (gs.take j)) := by
  unfold foldS
  rw [← List.foldl_append, List.take_append_drop]

lemma foldS_take (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) (j i : ℕ) (hi : i < j)
    (hj : j ≤ gs.length) : (foldS F (gs.take j)).getD i [] = (foldS F gs).getD i [] := by
  rw [foldS_split F gs j, foldl_prefix]
  rw [foldS_length]; simp; omega

lemma foldS_self (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) : (foldS F gs).getD j [] = F (foldS F (gs.take j)) gs[j] := by
  rw [foldS_split F gs j, List.drop_eq_getElem_cons hj, List.foldl_cons, foldl_prefix]
  · have hl : (foldS F (gs.take j)).length = j := by rw [foldS_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl]
  · simp [foldS_length]; omega

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ hj]

def coneF (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ := (coneStep n cs g).getD cs.length []

lemma cones_eq (n : ℕ) (C : Circuit) : cones n C = foldS (coneF n) C.gates := by
  unfold cones foldS
  have : coneStep n = fun cs g => cs ++ [coneF n cs g] := by
    funext cs g; unfold coneF coneStep; simp
  rw [this]

lemma coneF_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) : coneF n cs g =
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) []) := by
  unfold coneF coneStep; simp

lemma cones_get (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  rw [cones_eq, foldS_self _ _ _ hj, gateAt_eq C j hj, coneF_eq]
  have hl : (foldS (coneF n) (C.gates.take j)).length = j := by
    rw [foldS_length]; simp; omega
  rw [hl]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  rw [foldS_take _ _ _ _ (by omega) hj.le]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  rw [cones_eq, foldS_length]

lemma cone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i hi
    unfold InCone at hi
    by_cases hj : j < C.gates.length
    · rw [cones_get n C j hj] at hi
      obtain ⟨w, hw, hiw⟩ := List.mem_flatMap.mp hi
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      rcases List.mem_cons.mp hiw with h | h
      · omega
      · have := ih (w - n) (by omega) i h; omega
    · rw [List.getD_eq_default _ _ (by rw [cones_length]; omega)] at hi
      simp at hi

lemma cone_input (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (r : ℕ)
    (hr : r ∈ (gateAt C j).inputs) (h1 : n ≤ r) (h2 : r < n + j) :
    InCone n C (r - n) j ∧ ∀ k, InCone n C k (r - n) → InCone n C k j := by
  unfold InCone
  rw [cones_get n C j hj]
  constructor
  · exact List.mem_flatMap.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp [h1, h2]⟩, List.mem_cons_self⟩
  · intro k hk
    exact List.mem_flatMap.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp [h1, h2]⟩, List.mem_cons_of_mem _ hk⟩

lemma cone_trans (n : ℕ) (C : Circuit) : ∀ j i k, InCone n C k i → InCone n C i j → InCone n C k j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i k hki hij
    have hij' := hij
    unfold InCone at hij
    by_cases hj : j < C.gates.length
    · rw [cones_get n C j hj] at hij
      obtain ⟨w, hw, hiw⟩ := List.mem_flatMap.mp hij
      have hw' := hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw'
      unfold InCone
      rw [cones_get n C j hj]
      refine List.mem_flatMap.mpr ⟨w, hw, ?_⟩
      rcases List.mem_cons.mp hiw with h | h
      · subst h; exact List.mem_cons_of_mem _ hki
      · exact List.mem_cons_of_mem _ (ih (w - n) (by omega) i k hki h)
    · rw [List.getD_eq_default _ _ (by rw [cones_length]; omega)] at hij
      simp at hij

lemma wire_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : n + C.gates.length ≤ r) :
    wireVal n C r x = false := by
  change (run C.gates (List.ofFn x)).getD r false = false
  exact List.getD_eq_default _ _ (by rw [run_length]; simp; omega)

lemma wire_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < n) :
    wireVal n C r x = x ⟨r, hr⟩ := by
  change (run C.gates (List.ofFn x)).getD r false = _
  have hp : r < (List.ofFn x).length := by simpa using hr
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma wire_mono {n : ℕ} (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ v, x v = true → y v = true) : ∀ r, wireVal n C r x = true → wireVal n C r y = true := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hx
    by_cases hrn : r < n
    · rw [wire_input C x r hrn] at hx; rw [wire_input C y r hrn]; exact hxy _ hx
    · obtain ⟨j, rfl⟩ : ∃ j, r = n + j := ⟨r - n, by omega⟩
      by_cases hj : j < C.gates.length
      · rw [wireVal_gate, gateVal_eq C x j hj] at hx
        rw [wireVal_gate, gateVal_eq C y j hj]
        have hop := (hM _ (gateAt_mem C j hj)).1
        have step : ∀ s ∈ (gateAt C j).inputs, (if s < n + j then wireVal n C s x else false) = true →
            (if s < n + j then wireVal n C s y else false) = true := by
          intro s _ hs
          by_cases hsj : s < n + j
          · simp only [hsj, ite_true] at hs ⊢; exact ih s hsj hs
          · simp only [hsj, ite_false] at hs; exact absurd hs (by simp)
        rcases hop with hop | hop
        · rw [Set.mem_singleton_iff.mp hop] at hx ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hx ⊢
          exact fun s hs => step s hs (hx s hs)
        · rw [Set.mem_singleton_iff.mp hop] at hx ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hx ⊢
          obtain ⟨s, hs, hv⟩ := hx
          exact ⟨s, hs, step s hs hv⟩
      · rw [wire_beyond C x _ (by omega)] at hx; exact absurd hx (by simp)

lemma pair_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma split_val {n : ℕ} (C : Circuit) (hM : Monotone2 C) (j : ℕ) (u v : Fin n)
    (hown : ∀ i < j, InCone n C i j → (gateAt C i).op = GateOp.and → gateVal n C i (pairInput u v) = false) :
    ∀ r, (n ≤ r → InCone n C (r - n) j) → wireVal n C r (pairInput u v) = true →
      wireVal n C r (pairInput u u) = true ∨ wireVal n C r (pairInput v v) = true := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hc hx
    by_cases hrn : r < n
    · rw [wire_input C _ r hrn, pair_true] at hx
      rw [wire_input C _ r hrn, wire_input C _ r hrn, pair_true, pair_true]
      rcases hx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · obtain ⟨i, rfl⟩ : ∃ i, r = n + i := ⟨r - n, by omega⟩
      have hci : InCone n C i j := by have := hc (by omega); simpa using this
      have hij : i < j := cone_lt n C j i hci
      by_cases hi : i < C.gates.length
      · have hop := (hM _ (gateAt_mem C i hi)).1
        rcases hop with hop | hop
        · have := hown i hij hci (Set.mem_singleton_iff.mp hop)
          rw [wireVal_gate, this] at hx; exact absurd hx (by simp)
        · have hor : (gateAt C i).op = GateOp.or := Set.mem_singleton_iff.mp hop
          rw [wireVal_gate, gateVal_eq C _ i hi, hor] at hx
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hx
          obtain ⟨s, hs, hv⟩ := hx
          by_cases hsi : s < n + i
          · simp only [hsi, ite_true] at hv
            have hcs : n ≤ s → InCone n C (s - n) j := by
              intro hns
              exact cone_trans n C j i (s - n) (cone_input n C i hi s hs hns hsi).1 hci
            have hgo : ∀ y : Fin n → Bool, wireVal n C s y = true → wireVal n C (n + i) y = true := by
              intro y hy
              rw [wireVal_gate, gateVal_eq C _ i hi, hor]
              simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
              exact ⟨s, hs, by simp only [hsi, ite_true]; exact hy⟩
            rcases ih s (by omega) hcs hv with h | h
            · exact Or.inl (hgo _ h)
            · exact Or.inr (hgo _ h)
          · simp only [hsi, ite_false] at hv; exact absurd hv (by simp)
      · rw [wire_beyond C _ _ (by omega)] at hx; exact absurd hx (by simp)


lemma val_mono {n : ℕ} (C : Circuit) (hM : Monotone2 C) (j r : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ v, x v = true → y v = true) (h : (if r < n + j then wireVal n C r x else false) = true) :
    (if r < n + j then wireVal n C r y else false) = true := by
  by_cases hr : r < n + j
  · simp only [hr, ite_true] at h ⊢; exact wire_mono C hM x y hxy r h
  · simp [hr] at h

end PEqualNP.Outside.L_meta_1600

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_1600 in
theorem PEqualNP.Outside.L_meta_1600 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∀ j : ℕ, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C j x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) → (∀ u v : Fin n, G.Adj u v → ¬ PEqualNP.EdgeOwnership.Owns n C j u v) ∨ ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → PEqualNP.EdgeOwnership.Owns n C j p q → p = s ∨ q = s := by
  intro n G _ h4 C hM j hj hand hG
  set l := (gateAt C j).inputs with hl
  have hgv : ∀ x : Fin n → Bool, gateVal n C j x =
      l.all (fun r => if r < n + j then wireVal n C r x else false) := by
    intro x
    rw [gateVal_eq C x j hj, hand]
    simp [GateOp.eval, List.all_map, hl]
  have hsingle : ∀ w : Fin n, gateVal n C j (pairInput w w) = false := by
    intro w
    by_contra hc
    have := hG _ (by simpa using hc)
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, pair_true, or_self] at this
    obtain ⟨p, q, hpq, rfl, rfl⟩ := this
    exact G.irrefl hpq
  have hcross : ∀ a b : Fin n, gateVal n C j (pairInput a b) = true → G.Adj a b := by
    intro a b h
    have := hG _ h
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, pair_true] at this
    obtain ⟨p, q, hpq, hp, hq⟩ := this
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd hpq (G.irrefl)
    · exact hpq
    · exact hpq.symm
    · exact absurd hpq (G.irrefl)
  have hsplit : ∀ u v : Fin n, Owns n C j u v → ∀ r ∈ l,
      (if r < n + j then wireVal n C r (pairInput u u) else false) = true ∨
      (if r < n + j then wireVal n C r (pairInput v v) else false) = true := by
    intro u v ho r hr
    have hall := ho.2.2.1
    rw [hgv] at hall
    have hv := List.all_eq_true.mp hall r hr
    by_cases hrj : r < n + j
    · simp only [hrj, ite_true] at hv ⊢
      exact split_val C hM j u v ho.2.2.2 r
        (fun hnr => (cone_input n C j hj r hr hnr hrj).1) hv
    · simp [hrj] at hv
  have hlen : l.length ≤ 2 := (hM _ (gateAt_mem C j hj)).2
  have hpu : ∀ a b : Fin n, ∀ v, pairInput a a v = true → pairInput a b v = true := by
    intro a b v h; rw [pair_true] at h ⊢; exact Or.inl (h.elim id id)
  have hpv : ∀ a b : Fin n, ∀ v, pairInput b b v = true → pairInput a b v = true := by
    intro a b v h; rw [pair_true] at h ⊢; exact Or.inr (h.elim id id)
  match hm : l, hlen with
  | [], _ =>
    left
    intro u v _ ho
    have := hsingle u
    rw [hgv] at this
    simp at this
  | [r], _ =>
    left
    intro u v _ ho
    rcases hsplit u v ho r (by simp) with h | h
    · have := hsingle u; rw [hgv] at this
      simp only [List.all_cons, List.all_nil, Bool.and_true] at this
      rw [h] at this; exact absurd this (by simp)
    · have := hsingle v; rw [hgv] at this
      simp only [List.all_cons, List.all_nil, Bool.and_true] at this
      rw [h] at this; exact absurd this (by simp)
  | [r, s], _ =>
    have hrs : ∀ x : Fin n → Bool, gateVal n C j x =
        ((if r < n + j then wireVal n C r x else false) &&
          (if s < n + j then wireVal n C s x else false)) := by
      intro x; rw [hgv]; simp
    set R : Fin n → Prop := fun a => (if r < n + j then wireVal n C r (pairInput a a) else false) = true
    set S : Fin n → Prop := fun b => (if s < n + j then wireVal n C s (pairInput b b) else false) = true
    have hRS : ∀ a b, R a → S b → G.Adj a b := by
      intro a b ha hb
      apply hcross
      rw [hrs, Bool.and_eq_true]
      exact ⟨val_mono C hM j r _ _ (hpu a b) ha, val_mono C hM j s _ _ (hpv a b) hb⟩
    have hown : ∀ u v, Owns n C j u v → (R u ∧ S v) ∨ (R v ∧ S u) := by
      intro u v ho
      have h1 := hsplit u v ho r (by simp)
      have h2 := hsplit u v ho s (by simp)
      have nu := hsingle u
      have nv := hsingle v
      rw [hrs] at nu nv
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · rw [h1, h2] at nu; simp at nu
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · rw [h1, h2] at nv; simp at nv
    by_cases hno : ∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v
    · exact Or.inl hno
    · right
      push Not at hno
      obtain ⟨u0, v0, -, ho0⟩ := hno
      have hex : (∃ a, R a) ∧ ∃ b, S b := by
        rcases hown u0 v0 ho0 with h | h
        · exact ⟨⟨u0, h.1⟩, ⟨v0, h.2⟩⟩
        · exact ⟨⟨v0, h.1⟩, ⟨u0, h.2⟩⟩
      obtain ⟨⟨a0, ha0⟩, ⟨b0, hb0⟩⟩ := hex
      by_cases hR : ∀ a a', R a → R a' → a = a'
      · refine ⟨a0, fun p q _ ho => ?_⟩
        rcases hown p q ho with h | h
        · exact Or.inl (hR p a0 h.1 ha0)
        · exact Or.inr (hR q a0 h.1 ha0)
      · push Not at hR
        obtain ⟨a1, a2, ha1, ha2, hne⟩ := hR
        have hS : ∀ b b', S b → S b' → b = b' := by
          intro b1 b2 hb1 hb2
          by_contra hb
          exact h4 a1 b1 a2 b2 hne hb ⟨hRS a1 b1 ha1 hb1, (hRS a2 b1 ha2 hb1).symm,
            hRS a2 b2 ha2 hb2, (hRS a1 b2 ha1 hb2).symm⟩
        refine ⟨b0, fun p q _ ho => ?_⟩
        rcases hown p q ho with h | h
        · exact Or.inr (hS q b0 h.2 hb0)
        · exact Or.inl (hS p b0 h.2 hb0)
