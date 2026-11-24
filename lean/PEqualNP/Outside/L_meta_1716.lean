import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1716

open PEqualNP.CircuitLowerBounds

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

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true)
    (hN : ∀ k, ∀ hk : k < C.gates.length,
      ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
      value C x (n + k) = true → value C y (n + k) = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact hN (w - n) hk hop
    · simp [missing_value C x w (by unfold Circuit.size; omega)]


lemma andOr_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  apply mono C x y hxy
  intro k hk hn
  exact (hn (hC _ (List.getElem_mem hk))).elim



def ev {N : ℕ} (C : Circuit) (X Y : Finset (Fin N)) : Bool :=
  PEqualNP.MetaComplexity.circuitFun (N+N) C
    (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ Y)))

lemma ev_mono {N : ℕ} (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    {X Y X' Y' : Finset (Fin N)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    ev C X Y = true → ev C X' Y' = true := by
  apply andOr_mono C hC _ _ _ C.output
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p hp
    simp only [Fin.append_left, decide_eq_true_eq] at hp ⊢
    exact hX hp
  · intro p hp
    simp only [Fin.append_right, decide_eq_true_eq] at hp ⊢
    exact hY hp

lemma ev_false {N : ℕ} (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    {X Y X' Y' : Finset (Fin N)} (hX : X ⊆ X') (hY : Y ⊆ Y')
    (hf : ev C X' Y' = false) : ev C X Y = false := by
  cases he : ev C X Y with
  | false => rfl
  | true => have ht := ev_mono C hC hX hY he; rw [hf] at ht; contradiction

set_option maxHeartbeats 800000 in
theorem prove : ∀ (N82 K82 v82 : ℕ) (I82 : Fin N82 → Fin N82 → Prop) [DecidableRel I82] (Cs82 : Fin v82 → PEqualNP.CircuitLowerBounds.Circuit) (A82 : Finset (Fin v82)) (iz82 : Fin v82) (S82 W82 B82 : Finset (Fin N82)), (∀ i82 : Fin v82, (∀ g82 ∈ (Cs82 i82).gates, (g82.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g82.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g82.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N82 + N82) (Cs82 i82)) → iz82 ∈ A82 → Disjoint W82 B82 → (∀ p82 ∈ S82, ∀ l82 ∈ B82, ¬ I82 p82 l82) → (∀ X82 Y82 : Finset (Fin N82), X82 ⊆ S82 → Y82 ⊆ W82 → Y82.card ≤ K82 → (∀ p82a ∈ X82, ∀ l82a ∈ Y82, ¬ I82 p82a l82a) → ∃ i82a ∈ A82, PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 i82a) (Fin.append (fun a82 => decide (a82 ∈ X82)) (fun b82 => decide (b82 ∈ (Y82 ∪ B82)))) = false) → (∀ pz82 ∈ S82, ∀ T82 ⊆ W82, (∀ l82b ∈ T82, ¬ I82 pz82 l82b) → T82.card ≤ K82 → PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 iz82) (Fin.append (fun a82a => decide (a82a ∈ ({pz82} : Finset (Fin N82)))) (fun b82a => decide (b82a ∈ (T82 ∪ B82)))) = true → ∀ X82a Y82a : Finset (Fin N82), X82a ⊆ S82.filter (fun u82 => u82 ≠ pz82 ∧ ∀ l82c ∈ T82, ¬ I82 u82 l82c) → Y82a ⊆ W82.filter (fun l82d => ¬ I82 pz82 l82d ∧ l82d ∉ T82) → Y82a.card + T82.card ≤ K82 → (∀ p82b ∈ X82a, ∀ l82e ∈ Y82a, ¬ I82 p82b l82e) → ∃ i82b ∈ A82.erase iz82, PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 i82b) (Fin.append (fun a82b => decide (a82b ∈ X82a)) (fun b82b => decide (b82b ∈ (Y82a ∪ (T82 ∪ B82))))) = false) ∧ (∀ wz82 ∈ W82, ∀ Q82 ⊆ S82, (∀ p82c ∈ Q82, ¬ I82 p82c wz82) → PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 iz82) (Fin.append (fun a82c => decide (a82c ∈ Q82)) (fun b82c => decide (b82c ∈ (insert wz82 B82)))) = true → ∀ X82b Y82b : Finset (Fin N82), X82b ⊆ S82.filter (fun u82a => ¬ I82 u82a wz82 ∧ u82a ∉ Q82) → Y82b ⊆ W82.filter (fun l82f => l82f ≠ wz82 ∧ ∀ p82d ∈ Q82, ¬ I82 p82d l82f) → Y82b.card + 1 ≤ K82 → (∀ p82e ∈ X82b, ∀ l82g ∈ Y82b, ¬ I82 p82e l82g) → ∃ i82c ∈ A82.erase iz82, PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 i82c) (Fin.append (fun a82d => decide (a82d ∈ X82b)) (fun b82d => decide (b82d ∈ (Y82b ∪ insert wz82 B82)))) = false) := by
  classical
  intro N K v I inst Cs A iz S W B hCs hiz hdis hSB hsound
  have hC (i : Fin v) : PEqualNP.EdgeOwnership.AndOrOnly (Cs i) :=
    fun g hg => ((hCs i).1 g hg).1
  constructor
  · intro p hp T hT hIpT hTc ht X Y hX hY hcard hno
    change ev (Cs iz) {p} (T ∪ B) = true at ht
    have hXX : insert p X ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hp
      · exact (Finset.mem_filter.mp (hX hz)).1
    have hYY : Y ∪ T ⊆ W := by
      intro l hl
      rcases Finset.mem_union.mp hl with hl | hl
      · exact (Finset.mem_filter.mp (hY hl)).1
      · exact hT hl
    have hcount : (Y ∪ T).card ≤ K := (Finset.card_union_le Y T).trans hcard
    have hnone : ∀ z ∈ insert p X, ∀ l ∈ Y ∪ T, ¬ I z l := by
      intro z hz l hl
      rcases Finset.mem_insert.mp hz with rfl | hz
      · rcases Finset.mem_union.mp hl with hl | hl
        · exact (Finset.mem_filter.mp (hY hl)).2.1
        · exact hIpT l hl
      · rcases Finset.mem_union.mp hl with hl | hl
        · exact hno z hz l hl
        · exact (Finset.mem_filter.mp (hX hz)).2.2 l hl
    obtain ⟨i,hi,hf⟩ := hsound (insert p X) (Y ∪ T) hXX hYY hcount hnone
    change ev (Cs i) (insert p X) ((Y ∪ T) ∪ B) = false at hf
    have hit : ev (Cs iz) (insert p X) ((Y ∪ T) ∪ B) = true := by
      apply ev_mono (Cs iz) (hC iz) (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) ?_ ht
      intro l hl
      simp only [Finset.mem_union] at hl ⊢
      tauto
    have hne : i ≠ iz := by
      intro he
      subst i
      rw [hf] at hit
      contradiction
    refine ⟨i,Finset.mem_erase.mpr ⟨hne,hi⟩,?_⟩
    apply ev_false (Cs i) (hC i) (Finset.subset_insert _ _) ?_ hf
    intro l hl
    simpa only [Finset.union_assoc] using hl
  · intro z hz Q hQ hIQ ht X Y hX hY hcard hno
    change ev (Cs iz) Q (insert z B) = true at ht
    have hXX : X ∪ Q ⊆ S := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp (hX hp)).1
      · exact hQ hp
    have hYY : insert z Y ⊆ W := by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hz
      · exact (Finset.mem_filter.mp (hY hl)).1
    have hcount : (insert z Y).card ≤ K := (Finset.card_insert_le z Y).trans hcard
    have hnone : ∀ p ∈ X ∪ Q, ∀ l ∈ insert z Y, ¬ I p l := by
      intro p hp l hl
      rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_insert.mp hl with rfl | hl
        · exact (Finset.mem_filter.mp (hX hp)).2.1
        · exact hno p hp l hl
      · rcases Finset.mem_insert.mp hl with rfl | hl
        · exact hIQ p hp
        · exact (Finset.mem_filter.mp (hY hl)).2.2 p hp
    obtain ⟨i,hi,hf⟩ := hsound (X ∪ Q) (insert z Y) hXX hYY hcount hnone
    change ev (Cs i) (X ∪ Q) ((insert z Y) ∪ B) = false at hf
    have hit : ev (Cs iz) (X ∪ Q) ((insert z Y) ∪ B) = true := by
      apply ev_mono (Cs iz) (hC iz) (Finset.subset_union_right) ?_ ht
      intro l hl
      simp only [Finset.mem_insert,Finset.mem_union] at hl ⊢
      tauto
    have hne : i ≠ iz := by
      intro he
      subst i
      rw [hf] at hit
      contradiction
    refine ⟨i,Finset.mem_erase.mpr ⟨hne,hi⟩,?_⟩
    apply ev_false (Cs i) (hC i) Finset.subset_union_left ?_ hf
    intro l hl
    simp only [Finset.mem_insert,Finset.mem_union] at hl ⊢
    tauto

set_option maxHeartbeats 800000 in
theorem two_prove : ∀ (N8 K8 : ℕ) (I8 : Fin N8 → Fin N8 → Prop) [DecidableRel I8] (Ca8 Cb8 : PEqualNP.CircuitLowerBounds.Circuit) (S8 W8 : Finset (Fin N8)), (∀ g8 ∈ Ca8.gates, (g8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Ca8 → (∀ g8a ∈ Cb8.gates, (g8a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8a.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Cb8 → (∀ X8 Y8 : Finset (Fin N8), X8 ⊆ S8 → Y8 ⊆ W8 → Y8.card ≤ K8 → (∀ p8 ∈ X8, ∀ l8 ∈ Y8, ¬ I8 p8 l8) → (PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8 => decide (a8 ∈ X8)) (fun b8 => decide (b8 ∈ Y8))) && PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8a => decide (a8a ∈ X8)) (fun b8a => decide (b8a ∈ Y8)))) = false) → (∀ pz8 ∈ S8, ∀ T8 ⊆ W8, (∀ l8a ∈ T8, ¬ I8 pz8 l8a) → T8.card ≤ K8 → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8b => decide (a8b ∈ ({pz8} : Finset (Fin N8)))) (fun b8b => decide (b8b ∈ T8))) = true → ∀ X8a Y8a : Finset (Fin N8), X8a ⊆ S8.filter (fun u8 => u8 ≠ pz8 ∧ ∀ l8b ∈ T8, ¬ I8 u8 l8b) → Y8a ⊆ W8.filter (fun l8c => ¬ I8 pz8 l8c ∧ l8c ∉ T8) → Y8a.card + T8.card ≤ K8 → (∀ p8a ∈ X8a, ∀ l8d ∈ Y8a, ¬ I8 p8a l8d) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8c => decide (a8c ∈ X8a)) (fun b8c => decide (b8c ∈ (Y8a ∪ T8)))) = false) ∧ (∀ wz8 ∈ W8, ∀ Q8 ⊆ S8, (∀ p8b ∈ Q8, ¬ I8 p8b wz8) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8d => decide (a8d ∈ Q8)) (fun b8d => decide (b8d ∈ ({wz8} : Finset (Fin N8))))) = true → ∀ X8b Y8b : Finset (Fin N8), X8b ⊆ S8.filter (fun u8a => ¬ I8 u8a wz8 ∧ u8a ∉ Q8) → Y8b ⊆ W8.filter (fun l8e => l8e ≠ wz8 ∧ ∀ p8c ∈ Q8, ¬ I8 p8c l8e) → Y8b.card + 1 ≤ K8 → (∀ p8e ∈ X8b, ∀ l8f ∈ Y8b, ¬ I8 p8e l8f) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8e => decide (a8e ∈ X8b)) (fun b8e => decide (b8e ∈ (insert wz8 Y8b)))) = false) := by
  classical
  intro N K I inst Ca Cb S W hCa hCab hCb hCbb hs
  have hh := prove N K 2 I ![Ca,Cb] Finset.univ (1 : Fin 2) S W ∅
    (by intro i; fin_cases i; exact ⟨hCa,hCab⟩; exact ⟨hCb,hCbb⟩)
    (by simp) (by simp) (by simp)
    (by
      intro X Y hX hY hcard hno
      have hf := hs X Y hX hY hcard hno
      rw [Bool.and_eq_false_iff] at hf
      rcases hf with hf | hf
      · refine ⟨0,by simp,?_⟩
        simpa using hf
      · refine ⟨1,by simp,?_⟩
        simpa using hf)
  constructor
  · intro p hp T hT hno hTc ht X Y hX hY hcard hXY
    obtain ⟨i,hi,hf⟩ := hh.1 p hp T hT hno hTc (by simpa using ht) X Y hX hY hcard hXY
    fin_cases i
    · simpa using hf
    · simp at hi
  · intro z hz Q hQ hno ht X Y hX hY hcard hXY
    obtain ⟨i,hi,hf⟩ := hh.2 z hz Q hQ hno (by simpa using ht) X Y hX hY hcard hXY
    fin_cases i
    · simpa [Finset.union_comm] using hf
    · simp at hi

end PEqualNP.Outside.L_meta_1716

theorem PEqualNP.Outside.L_meta_1716 : ∀ (N8 K8 : ℕ) (I8 : Fin N8 → Fin N8 → Prop) [DecidableRel I8] (Ca8 Cb8 : PEqualNP.CircuitLowerBounds.Circuit) (S8 W8 : Finset (Fin N8)), (∀ g8 ∈ Ca8.gates, (g8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Ca8 → (∀ g8a ∈ Cb8.gates, (g8a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8a.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Cb8 → (∀ X8 Y8 : Finset (Fin N8), X8 ⊆ S8 → Y8 ⊆ W8 → Y8.card ≤ K8 → (∀ p8 ∈ X8, ∀ l8 ∈ Y8, ¬ I8 p8 l8) → (PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8 => decide (a8 ∈ X8)) (fun b8 => decide (b8 ∈ Y8))) && PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8a => decide (a8a ∈ X8)) (fun b8a => decide (b8a ∈ Y8)))) = false) → (∀ pz8 ∈ S8, ∀ T8 ⊆ W8, (∀ l8a ∈ T8, ¬ I8 pz8 l8a) → T8.card ≤ K8 → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8b => decide (a8b ∈ ({pz8} : Finset (Fin N8)))) (fun b8b => decide (b8b ∈ T8))) = true → ∀ X8a Y8a : Finset (Fin N8), X8a ⊆ S8.filter (fun u8 => u8 ≠ pz8 ∧ ∀ l8b ∈ T8, ¬ I8 u8 l8b) → Y8a ⊆ W8.filter (fun l8c => ¬ I8 pz8 l8c ∧ l8c ∉ T8) → Y8a.card + T8.card ≤ K8 → (∀ p8a ∈ X8a, ∀ l8d ∈ Y8a, ¬ I8 p8a l8d) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8c => decide (a8c ∈ X8a)) (fun b8c => decide (b8c ∈ (Y8a ∪ T8)))) = false) ∧ (∀ wz8 ∈ W8, ∀ Q8 ⊆ S8, (∀ p8b ∈ Q8, ¬ I8 p8b wz8) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8d => decide (a8d ∈ Q8)) (fun b8d => decide (b8d ∈ ({wz8} : Finset (Fin N8))))) = true → ∀ X8b Y8b : Finset (Fin N8), X8b ⊆ S8.filter (fun u8a => ¬ I8 u8a wz8 ∧ u8a ∉ Q8) → Y8b ⊆ W8.filter (fun l8e => l8e ≠ wz8 ∧ ∀ p8c ∈ Q8, ¬ I8 p8c l8e) → Y8b.card + 1 ≤ K8 → (∀ p8e ∈ X8b, ∀ l8f ∈ Y8b, ¬ I8 p8e l8f) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8e => decide (a8e ∈ X8b)) (fun b8e => decide (b8e ∈ (insert wz8 Y8b)))) = false) :=
  PEqualNP.Outside.L_meta_1716.two_prove
