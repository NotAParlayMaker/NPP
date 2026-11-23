import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_792_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_initial (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_initial gs w
  rw [ht]; simp [hl]

theorem initial_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_initial gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, initial_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact initial_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [initial_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Splits {α : Type} [DecidableEq α] (L : ℕ → Finset α) (G : Finset ℕ) (w : ℕ) : Prop :=
  ∃ D : Finset ℕ, D.card ≤ 2 ∧ L w ⊆ D.biUnion L ∧
    ∀ z ∈ D, z < w ∧ (z ∈ G ∨ (L z).card ≤ 1)

lemma frontier {α : Type} [DecidableEq α] (L : ℕ → Finset α) (G : Finset ℕ)
    (hs : ∀ w ∈ G, Splits L G w) (F : Finset ℕ)
    (hf : ∀ w ∈ F, w ∈ G ∨ (L w).card ≤ 1) :
    (F.biUnion L).card ≤ G.card + F.card := by
  classical
  induction G using Finset.induction_on_max generalizing F with
  | empty =>
    calc
      (F.biUnion L).card ≤ ∑ w ∈ F, (L w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ F, 1 := Finset.sum_le_sum fun w hw => by simpa using hf w hw
      _ = _ := by simp
  | insert w G hmax ih =>
    have hwG : w ∉ G := fun h => (hmax w h).false
    have shrink {z : ℕ} (hz : z ≠ w)
        (h : z ∈ insert w G ∨ (L z).card ≤ 1) : z ∈ G ∨ (L z).card ≤ 1 := by
      simpa [hz] using h
    have hs' : ∀ z ∈ G, Splits L G z := by
      intro z hz
      obtain ⟨D, hcard, hcov, hD⟩ := hs z (Finset.mem_insert_of_mem hz)
      refine ⟨D, hcard, hcov, ?_⟩
      intro a ha
      obtain ⟨haz, h⟩ := hD a ha
      exact ⟨haz, shrink (haz.trans (hmax z hz)).ne h⟩
    by_cases hwF : w ∈ F
    · obtain ⟨D, hcard, hcov, hD⟩ := hs w (Finset.mem_insert_self ..)
      let F' := F.erase w ∪ D
      have hsub : F.biUnion L ⊆ F'.biUnion L := by
        intro p hp
        obtain ⟨z, hz, hpz⟩ := Finset.mem_biUnion.mp hp
        by_cases hzw : z = w
        · subst z
          obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.mp (hcov hpz)
          exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_union_right _ ha, hpa⟩
        · exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzw, hz⟩), hpz⟩
      have hf' : ∀ z ∈ F', z ∈ G ∨ (L z).card ≤ 1 := by
        intro z hz
        rcases Finset.mem_union.mp hz with he | hd
        · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp he
          exact shrink hne (hf z hmem)
        · exact shrink (hD z hd).1.ne (hD z hd).2
      have bound := (Finset.card_le_card hsub).trans (ih hs' F' hf')
      have hsize : F'.card ≤ (F.erase w).card + D.card := Finset.card_union_le _ _
      rw [Finset.card_insert_of_notMem hwG]
      have hrem := Finset.card_erase_add_one hwF
      omega
    · have hf' : ∀ z ∈ F, z ∈ G ∨ (L z).card ≤ 1 := by
        intro z hz
        exact shrink (fun h => hwF (h ▸ hz)) (hf z hz)
      have h := ih hs' F hf'
      rw [Finset.card_insert_of_notMem hwG]
      omega

def one {n : ℕ} (p : Fin n) (q : Fin n) : Bool := decide (q = p)

def indices (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => val C (one p) w = true

lemma mem_indices {n : ℕ} {C : Circuit} {w : ℕ} {p : Fin n} :
    p ∈ indices n C w ↔ val C (one p) w = true := by simp [indices]

lemma small_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (indices n C w).card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro p q hp hq
  have h (t : Fin n) (ht : t ∈ indices n C w) : (⟨w, hw⟩ : Fin n) = t := by
    have hv := mem_indices.mp ht
    rw [show w = (⟨w, hw⟩ : Fin n).val from rfl, val_input] at hv
    simpa [one] using hv
  exact (h p hp).symm.trans (h q hq)

lemma difference (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or)
    (a b c d : Bool) (ht : op.eval [a,b] = true) (hf : op.eval [c,d] = false) :
    (a = true ∧ c = false) ∨ (b = true ∧ d = false) := by
  rcases h with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [GateOp.eval]

lemma labelled_split {n j : ℕ} (C : Circuit) (ψ : ℕ → Bool) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2)
    (hψ : ψ (n+j) = g.op.eval (g.inputs.map (fun w => if w < n+j then ψ w else false)))
    (hf : ψ (n+j) = false) :
    ∃ D : Finset ℕ, D.card ≤ 2 ∧ indices n C (n+j) ⊆ D.biUnion (indices n C) ∧
      ∀ w ∈ D, w < n+j ∧ ψ w = false ∧ w ∈ g.inputs := by
  classical
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  let D := ({a,b} : Finset ℕ).filter fun w => w < n+j ∧ ψ w = false
  have hD {w : ℕ} : w ∈ D ↔ (w = a ∨ w = b) ∧ w < n+j ∧ ψ w = false := by simp [D]
  refine ⟨D, ?_, ?_, ?_⟩
  · exact (Finset.card_filter_le ..).trans (Finset.card_le_two)
  · intro p hp
    have ht := mem_indices.mp hp
    rw [val_gate C (one p) hg, hab] at ht
    rw [hf, hab] at hψ
    simp only [List.map_cons, List.map_nil] at ht hψ
    have lift (w : ℕ) (hm : w = a ∨ w = b) (hv : operand C (one p) (n+j) w = true)
        (hl : (if w < n+j then ψ w else false) = false) :
        p ∈ D.biUnion (indices n C) := by
      by_cases hw : w < n+j
      · refine Finset.mem_biUnion.mpr ⟨w, hD.mpr ⟨hm, hw, by simpa [hw] using hl⟩, ?_⟩
        exact mem_indices.mpr (by simpa [operand, hw] using hv)
      · simp [operand, hw] at hv
    rcases difference g.op hop _ _ _ _ ht hψ.symm with h | h
    · exact lift a (Or.inl rfl) h.1 h.2
    · exact lift b (Or.inr rfl) h.1 h.2
  · intro w hw
    obtain ⟨hab', hlt, hfalse⟩ := hD.mp hw
    exact ⟨hlt, hfalse, by simpa [hab] using hab'⟩

end PEqualNP.Outside.L_meta_792_aux

open PEqualNP.Outside.L_meta_792_aux
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_792 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true → p ∈ S) → r ∈ Q → (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) → (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = false → (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (n + r) false = true)).card ≤ Q.card + 1 := by
  classical
  intro n r S C Q ψ hb _ hr hQ hclose hlabel hexit hroot
  let G := (Q.filter fun j => ψ (n+j) = false).image (fun j => n+j)
  have hmem {w : ℕ} : w ∈ G ↔ ∃ j ∈ Q, ψ (n+j) = false ∧ n+j = w := by
    simp [G, and_assoc]
  have hsplit : ∀ w ∈ G, Splits (indices n C) G w := by
    intro w hw
    obtain ⟨j, hj, hjf, rfl⟩ := hmem.mp hw
    have hbound : j < C.gates.length := (hQ j hj).1
    let g := C.gates[j]
    have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hbound
    obtain ⟨hop, hlen⟩ := hb g (List.getElem_mem hbound)
    obtain ⟨D, hd, hcov, hchild⟩ := labelled_split C ψ g hg hop hlen (hlabel j hj g hg) hjf
    refine ⟨D, hd, hcov, ?_⟩
    intro z hz
    obtain ⟨hlt, hfalse, hwire⟩ := hchild z hz
    refine ⟨hlt, ?_⟩
    by_cases hsmall : (indices n C z).card ≤ 1
    · exact Or.inr hsmall
    left
    by_cases hzin : z < n
    · exact (hsmall (small_input C z hzin)).elim
    let k := z-n
    have hk : n+k = z := by dsimp [k]; omega
    have hkj : k < j := by omega
    by_cases hkQ : k ∈ Q
    · exact hmem.mpr ⟨k, hkQ, hk ▸ hfalse, hk⟩
    have houtside : ∀ i ∈ Q, z ≠ n+i := by
      intro i hi heq
      have : k = i := by omega
      exact hkQ (this ▸ hi)
    have hS : indices n C z ⊆ S := hexit z houtside hfalse
    have hlarge : 2 ≤ (indices n C z).card := by omega
    rw [← hk] at hwire hS hlarge
    exact hmem.mpr ⟨k, hclose j hj k hkj ⟨g, hg, hwire⟩ hS hlarge, hk ▸ hfalse, hk⟩
  have hrg : n+r ∈ G := hmem.mpr ⟨r, hr, hroot, rfl⟩
  have H := frontier (indices n C) G hsplit {n+r} (by simpa using Or.inl hrg)
  have hcard : G.card ≤ Q.card := Finset.card_image_le.trans (Finset.card_filter_le ..)
  change (indices n C (n+r)).card ≤ Q.card + 1
  simpa using H.trans (Nat.add_le_add_right hcard _)
