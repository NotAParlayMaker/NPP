import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1654

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem wires_mono {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (i : ℕ)
    (h : (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD i false = true) :
    (Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD i false = true := by
  change (gates.foldl stp (List.ofFn x)).getD i false = true at h
  change (gates.foldl stp (List.ofFn y)).getD i false = true
  refine mono gates _ _ (by simp) hg ?_ i h
  intro k
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hk
  · exact hxy _
  · exact id

end PEqualNP.Outside.L_meta_1654

open PEqualNP.Outside.L_meta_1654 in
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
    v ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j := by
  intro n L line l gates G K I _ _ hg _ hno hI harc hK v hv hGv
  have hm := wires_mono (n := n) gates (fun g hg' => (hg g hg').1)
  have hvI : v ∉ I := by
    intro hvI
    apply hno
    refine ⟨I, hI, harc, ?_, hK⟩
    refine hm (fun u => decide (u = v)) (fun u => decide (u ∈ I)) ?_ G hGv
    intro u hu
    have hu' : u = v := by simpa using hu
    subst hu'
    simpa using hvI
  refine ⟨hvI, ?_⟩
  by_contra hsec
  apply hno
  refine ⟨insert v I, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_insert_left]
    exact ⟨hv, hI⟩
  · intro a ha b hb c hc hab hac hbc hex
    obtain ⟨j, haj, hbj, hcj⟩ := hex
    rw [Finset.mem_insert] at ha hb hc
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact hab (ha.trans hb.symm)
      · rcases hc with hc | hc
        · exact hac (ha.trans hc.symm)
        · exact hsec ⟨b, hb, c, hc, hbc, j, hbj, hcj, ha ▸ haj⟩
    · rcases hb with hb | hb
      · rcases hc with hc | hc
        · exact hbc (hb.trans hc.symm)
        · exact hsec ⟨a, ha, c, hc, hac, j, haj, hcj, hb ▸ hbj⟩
      · rcases hc with hc | hc
        · exact hsec ⟨a, ha, b, hb, hab, j, haj, hbj, hc ▸ hcj⟩
        · exact harc a ha b hb c hc hab hac hbc ⟨j, haj, hbj, hcj⟩
  · refine hm (fun u => decide (u = v)) (fun u => decide (u ∈ insert v I)) ?_ G hGv
    intro u hu
    have hu' : u = v := by simpa using hu
    simp [hu']
  · refine hm (fun u => decide (u ∈ I)) (fun u => decide (u ∈ insert v I)) ?_ K hK
    intro u hu
    have hu' : u ∈ I := by simpa using hu
    simp [hu']
