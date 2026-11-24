import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1654

open PEqualNP.CircuitLowerBounds

private def evalGates (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

private lemma evalGates_cons (g : Gate) (gs : List Gate) (xs : List Bool) :
    evalGates (g :: gs) xs =
      evalGates gs (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) :=
  rfl

private lemma evalGates_length (gs : List Gate) (xs : List Bool) :
    (evalGates gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalGates]
  | cons g gs ih =>
    rw [evalGates_cons, ih]
    simp
    omega

private lemma evalGates_prefix (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (evalGates gs xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalGates_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma evalGates_take_drop (gs : List Gate) (xs : List Bool) (k : ℕ) :
    evalGates gs xs = evalGates (gs.drop k) (evalGates (gs.take k) xs) := by
  simpa only [evalGates, List.foldl_append] using
    congrArg (fun l : List Gate => evalGates l xs) (List.take_append_drop k gs).symm

private def wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    wireVal C x p = x p := by
  change (evalGates C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [evalGates_prefix _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma wireVal_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wireVal C x w = false := by
  change (evalGates C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [evalGates_length] using hw)

private lemma wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.gates.length) :
    let g := C.gates[w - n]'(by omega)
    wireVal C x w = g.op.eval (g.inputs.map fun r => if r < w then wireVal C x r else false) := by
  let idx := w - n
  have hidx : idx < C.gates.length := by omega
  let g := C.gates[idx]
  let pref := evalGates (C.gates.take idx) (List.ofFn x)
  have hplen : pref.length = w := by
    simp [pref, evalGates_length, Nat.min_eq_left hidx.le, idx]
    omega
  have hsplit :
      evalGates C.gates (List.ofFn x) = evalGates (g :: C.gates.drop (idx + 1)) pref := by
    rw [evalGates_take_drop C.gates (List.ofFn x) idx, List.drop_eq_getElem_cons hidx]
  have hread (r : ℕ) : pref.getD r false = if r < w then wireVal C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change pref.getD r false = (evalGates C.gates (List.ofFn x)).getD r false
      rw [hsplit]
      exact (evalGates_prefix _ pref r (by omega)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (evalGates C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then wireVal C x r else false)
  rw (occs := [1]) [hsplit]
  rw (occs := [1]) [evalGates_cons]
  rw [evalGates_prefix _ _ _ (by simp [hplen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [hplen, Nat.sub_self, List.getD_cons_zero, hread]

private lemma gate_deps {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.gates.length) :
    ∃ D : Finset ℕ, D.card ≤ 2 ∧ (∀ r ∈ D, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ D, wireVal C x r = true → wireVal C y r = true) →
        wireVal C x w = true → wireVal C y w = true := by
  classical
  let g := C.gates[w - n]'(by omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let D := g.inputs.toFinset.filter (· < w)
  refine ⟨D, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hstep (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then wireVal C x r else false) = true →
        (if r < w then wireVal C y r else false) = true := by
      by_cases hlt : r < w
      · simpa [hlt] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hlt⟩)
      · simp [hlt]
    have hform (z : Fin n → Bool) :
        wireVal C z w = g.op.eval (g.inputs.map fun r => if r < w then wireVal C z r else false) :=
      wireVal_gate C z w hn hw
    rw [hform x] at hx
    rw [hform y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      exact hstep r hr (hx _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hbt⟩ := hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, hstep r hr hbt⟩

private lemma wireVal_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    wireVal C x w = true → wireVal C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change wireVal C x p = true → wireVal C y p = true
      simpa only [wireVal_input] using hxy p
    · by_cases hw : w < n + C.gates.length
      · obtain ⟨D, _, hD, hstep⟩ := gate_deps C hG w (by omega) hw
        exact hstep x y fun r hr => ih r (hD r hr)
      · simp [wireVal_oob C x w (by omega)]


private lemma extendArc {n N : ℕ} (line : Fin N → Finset (Fin n)) (I : Finset (Fin n)) (v : Fin n)
    (arc : ∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c →
      ¬ ∃ j, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j)
    (noSec : ¬ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j) :
    ∀ a ∈ insert v I, ∀ b ∈ insert v I, ∀ c ∈ insert v I, a ≠ b → a ≠ c → b ≠ c →
      ¬ ∃ j, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j := by
  intro a ha b hb c hc hab hac hbc
  rintro ⟨j,aj,bj,cj⟩
  by_cases av : a = v
  · subst a
    exact noSec ⟨b,Finset.mem_of_mem_insert_of_ne hb hab.symm,c,
      Finset.mem_of_mem_insert_of_ne hc hac.symm,hbc,j,bj,cj,aj⟩
  have aI := Finset.mem_of_mem_insert_of_ne ha av
  by_cases bv : b = v
  · subst b
    exact noSec ⟨a,aI,c,Finset.mem_of_mem_insert_of_ne hc hbc.symm,hac,j,aj,cj,bj⟩
  have bI := Finset.mem_of_mem_insert_of_ne hb bv
  by_cases cv : c = v
  · subst c
    exact noSec ⟨a,aI,b,bI,hab,j,aj,bj,cj⟩
  exact arc a aI b bI c (Finset.mem_of_mem_insert_of_ne hc cv) hab hac hbc ⟨j,aj,bj,cj⟩

end PEqualNP.Outside.L_meta_1654

theorem PEqualNP.Outside.L_meta_1654 : ∀ (n L : ℕ) (line : Fin L → Finset (Fin n)) (l : Fin L) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G K : ℕ) (I : Finset (Fin n)),
  (∀ p r : Fin n, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
  (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (¬ ∃ X : Finset (Fin n), Disjoint X (line l) ∧
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true) →
  Disjoint I (line l) →
  (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ I)))).getD K false = true →
  ∀ v : Fin n, v ∉ line l →
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = v)))).getD G false = true →
    v ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j
:= by
  classical
  intro n N line l gates G K I _ _ basis _ excludeBoth off arc hon v vOff vOn
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,0⟩
  have mono (x y : Fin n → Bool) (h : ∀ p, x p = true → y p = true) (w : ℕ) :=
    PEqualNP.Outside.L_meta_1654.wireVal_mono C basis x y h w
  constructor
  · intro mem
    apply excludeBoth
    refine ⟨I,off,arc,?_,hon⟩
    apply mono (fun u => decide (u = v)) (fun u => decide (u ∈ I)) _ G vOn
    intro p hp
    have eq : p = v := of_decide_eq_true hp
    subst p
    exact decide_eq_true mem
  · by_contra noSec
    apply excludeBoth
    refine ⟨insert v I,?_,PEqualNP.Outside.L_meta_1654.extendArc line I v arc noSec,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro x hx hl
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact vOff hl
      · exact Finset.disjoint_left.mp off hx hl
    · apply mono (fun u => decide (u = v)) (fun u => decide (u ∈ insert v I)) _ G vOn
      intro p hp
      have eq : p = v := of_decide_eq_true hp
      subst p
      exact decide_eq_true (Finset.mem_insert_self _ _)
    · apply mono (fun u => decide (u ∈ I)) (fun u => decide (u ∈ insert v I)) _ K hon
      intro p hp
      exact decide_eq_true (Finset.mem_insert_of_mem (of_decide_eq_true hp))
