import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925_aux

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

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

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

def bit {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (w : ℕ) : Bool :=
  val C (fun i => decide (i ∈ U)) w

lemma op_imp {g : Gate} (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ → Bool) (h : ∀ z ∈ g.inputs, a z = true → b z = true) :
    g.op.eval (g.inputs.map a) = true → g.op.eval (g.inputs.map b) = true := by
  rcases hop with ha | ha
  · simp only [ha, GateOp.eval, List.all_eq_true, List.forall_mem_map, id_eq]
    exact fun ht z hz => h z hz (ht z hz)
  · simp only [ha, GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨z,hz,ht⟩
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
    exact ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,h j hj ht⟩

lemma gate_imp {n j : ℕ} (C : Circuit) {g : Gate} (hg : C.gates[j]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (A B : Finset (Fin n))
    (h : ∀ z ∈ g.inputs, z < n+j → bit C A z = true → bit C B z = true) :
    bit C A (n+j) = true → bit C B (n+j) = true := by
  unfold bit
  rw [val_gate C _ hg, val_gate C _ hg]
  apply op_imp hop
  intro z hz
  by_cases hlt : z < n+j
  · simpa [operand,hlt, bit] using h z hz hlt
  · simp [operand,hlt]

lemma bit_mono {n : ℕ} (C : Circuit)
    (hgates : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {A B : Finset (Fin n)} (hAB : A ⊆ B) (w : ℕ) :
    bit C A w = true → bit C B w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · unfold bit
      rw [val_input C (fun i => decide (i ∈ A)) ⟨w,hin⟩,
        val_input C (fun i => decide (i ∈ B)) ⟨w,hin⟩]
      simp only [decide_eq_true_eq]
      exact fun h => hAB h
    by_cases hlast : w < n + C.gates.length
    · let j := w-n
      have hj : j < C.gates.length := by dsimp [j]; omega
      have he : n+j=w := by dsimp [j]; omega
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
      rw [← he]
      apply gate_imp C hg (hgates g (List.getElem_mem hj))
      intro z _ hz
      exact ih z (he ▸ hz)
    · have hv : bit C A w = false := val_beyond C _ (by omega)
      simp [hv]

def Branch {α : Type} (E : ℕ → α → Prop) (T : ℕ → Prop) (G : Finset ℕ) (w : ℕ) : Prop :=
  ∃ D : Finset ℕ, D.card ≤ 2 ∧ (∀ z ∈ D, z < w ∧ (z ∈ G ∨ T z)) ∧
    ∀ u, (∀ z ∈ D, E z u) → E w u

lemma frontier {α : Type} (E : ℕ → α → Prop) (T : ℕ → Prop) (G : Finset ℕ)
    (hs : ∀ w ∈ G, Branch E T G w) (F : Finset ℕ)
    (hf : ∀ w ∈ F, w ∈ G ∨ T w) :
    ∃ Z : Finset ℕ, Z.card ≤ G.card + F.card ∧ (∀ z ∈ Z, T z) ∧
      ∀ u, (∀ z ∈ Z, E z u) → ∀ w ∈ F, E w u := by
  classical
  induction G using Finset.induction_on_max generalizing F with
  | empty =>
    exact ⟨F, by simp, fun w hw => by simpa using hf w hw, fun _ h => h⟩
  | insert x G ltG ih =>
    have hnot : x ∉ G := fun h => (ltG x h).false
    have shrink {z : ℕ} (hz : z ≠ x) (h : z ∈ insert x G ∨ T z) : z ∈ G ∨ T z := by
      simpa [hz] using h
    have hs' (w : ℕ) (hw : w ∈ G) : Branch E T G w := by
      obtain ⟨D, hd, hD, hE⟩ := hs w (Finset.mem_insert_of_mem hw)
      exact ⟨D, hd, fun z hz => ⟨(hD z hz).1, shrink ((hD z hz).1.trans (ltG w hw)).ne (hD z hz).2⟩, hE⟩
    by_cases hx : x ∈ F
    · obtain ⟨D, hd, hD, hE⟩ := hs x (Finset.mem_insert_self ..)
      let F' := F.erase x ∪ D
      have hf' : ∀ z ∈ F', z ∈ G ∨ T z := by
        intro z hz
        rcases Finset.mem_union.mp hz with h | h
        · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp h
          exact shrink hne (hf z hmem)
        · exact shrink (hD z h).1.ne (hD z h).2
      obtain ⟨Z, hcard, hZ, hZE⟩ := ih hs' F' hf'
      refine ⟨Z, ?_, hZ, ?_⟩
      · have hsize : F'.card ≤ (F.erase x).card + D.card := Finset.card_union_le _ _
        have hrem := Finset.card_erase_add_one hx
        rw [Finset.card_insert_of_notMem hnot]
        omega
      · intro u hu w hw
        by_cases he : w=x
        · subst w
          exact hE u fun z hz => hZE u hu z (Finset.mem_union_right _ hz)
        · exact hZE u hu w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hw⟩))
    · have hf' : ∀ z ∈ F, z ∈ G ∨ T z := fun z hz => shrink (fun e => hx (e ▸ hz)) (hf z hz)
      obtain ⟨Z, hcard, hZ, hZE⟩ := ih hs' F hf'
      refine ⟨Z, ?_, hZ, hZE⟩
      rw [Finset.card_insert_of_notMem hnot]
      omega

def Allowed {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) (X : Finset (Fin n)) : Prop :=
  X.card ≤ 1 ∨ ∃ j, j ≠ i ∧ X = S j

lemma union_weight {n m q : ℕ} (hq : 2 ≤ q) (S : Fin m → Finset (Fin n))
    (hsize : ∀ j, (S j).card = q+1) (hpair : ∀ j k, j ≠ k → (S j ∩ S k).card = 1)
    (i : Fin m) (Z : Finset ℕ) (R : ℕ → Finset (Fin n))
    (ha : ∀ z ∈ Z, Allowed S i (R z)) :
    (Z.biUnion R).card ≤ Z.card * q + 1 := by
  classical
  by_cases hline : ∃ a ∈ Z, ∃ j, R a = S j
  · obtain ⟨a,haZ,j,hR⟩ := hline
    let F := (Z.erase a).biUnion fun z => R z \ S j
    have hsub : Z.biUnion R ⊆ S j ∪ F := by
      intro p hp
      obtain ⟨z,hz,hp⟩ := Finset.mem_biUnion.mp hp
      by_cases hj : p ∈ S j
      · exact Finset.mem_union_left _ hj
      · have hne : z ≠ a := by rintro rfl; exact hj (hR ▸ hp)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨z,Finset.mem_erase.mpr ⟨hne,hz⟩,Finset.mem_sdiff.mpr ⟨hp,hj⟩⟩)
    have hdiff (z : ℕ) (hz : z ∈ Z.erase a) : (R z \ S j).card ≤ q := by
      rcases ha z (Finset.mem_of_mem_erase hz) with h | ⟨k,_,hk⟩
      · exact (Finset.card_le_card Finset.sdiff_subset).trans (by omega)
      · rw [hk]
        by_cases he : k=j
        · simp [he]
        · have hsum := Finset.card_sdiff_add_card_inter (S k) (S j)
          rw [hsize, hpair k j he] at hsum
          omega
    have hF : F.card ≤ (Z.erase a).card*q := calc
      F.card ≤ ∑ z ∈ Z.erase a, (R z \ S j).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ Z.erase a, q := Finset.sum_le_sum hdiff
      _ = _ := by simp
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [hsize] at h
    rw [← Finset.card_erase_add_one haZ, Nat.add_mul, one_mul]
    omega
  · have hsmall (z : ℕ) (hz : z ∈ Z) : (R z).card ≤ 1 := by
      rcases ha z hz with h | ⟨j,_,hj⟩
      · exact h
      · exact (hline ⟨z,hz,j,hj⟩).elim
    calc
      (Z.biUnion R).card ≤ ∑ z ∈ Z, (R z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ Z, 1 := Finset.sum_le_sum hsmall
      _ = Z.card := by simp
      _ ≤ Z.card*q+1 := by
        have := Nat.mul_le_mul_left Z.card (show 1 ≤ q by omega)
        omega

lemma intersection_weight {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hpair : ∀ j k, j ≠ k → (S j ∩ S k).card = 1)
    (i : Fin m) (Z : Finset ℕ) (R : ℕ → Finset (Fin n))
    (ha : ∀ z ∈ Z, Allowed S i (R z)) :
    (Z.biUnion R ∩ S i).card ≤ Z.card := by
  have hsub : Z.biUnion R ∩ S i ⊆ Z.biUnion (fun z => R z ∩ S i) := by
    intro v hv
    obtain ⟨hz,hi⟩ := Finset.mem_inter.mp hv
    obtain ⟨z,hz,hv⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_inter.mpr ⟨hv,hi⟩⟩
  calc
    _ ≤ _ := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ Z, 1 := by
      apply Finset.sum_le_sum
      intro z hz
      rcases ha z hz with h | ⟨j,hj,he⟩
      · exact (Finset.card_le_card Finset.inter_subset_left).trans h
      · rw [he,hpair j i hj]
    _ = _ := by simp

end PEqualNP.Outside.L_meta_925_aux

open PEqualNP.Outside.L_meta_925_aux
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hsize hpair gates out hb hc c hcq hcK
  let C : Circuit := ⟨gates,0⟩
  let W := (Finset.range gates.length).image fun j => n+j
  let G (i : Fin m) := W.filter fun z =>
    bit C (S i) z = true ∧ ∀ j, j ≠ i → bit C (S j) z = false
  have hmono (g : Gate) (hg : g ∈ C.gates) := (hb g hg).1
  have output (i : Fin m) (U : Finset (Fin n)) (hu : U.card ≤ K) :
      bit C U (out i) = true ↔ S i ⊆ U := by
    have hset : (Finset.univ.filter fun v : Fin n => decide (v ∈ U) = true) = U := by ext; simp
    have h := hc i (fun v => decide (v ∈ U)) (by rw [hset]; exact hu)
    change bit C U (out i) = decide (∀ v ∈ S i, decide (v ∈ U) = true) at h
    rw [h]
    simp only [decide_eq_true_eq]
    exact ⟨fun h _ hv => h _ hv, fun h _ hv => h hv⟩
  have count (i : Fin m) : c ≤ (G i).card := by
    by_contra! hsmall
    have hcpos : 1 ≤ c := by omega
    have hqK : q+1 ≤ K := by
      have h := Nat.mul_le_mul_right q hcpos
      simp only [one_mul] at h
      omega
    let T (z : ℕ) := ∃ X : Finset (Fin n), Allowed S i X ∧ bit C X z = true
    have classify (z : ℕ) (hz : bit C (S i) z = true) : z ∈ G i ∨ T z := by
      by_cases hin : z < n
      · right
        let p : Fin n := ⟨z,hin⟩
        refine ⟨{p}, Or.inl (by simp), ?_⟩
        change val C (fun v => decide (v ∈ ({p} : Finset (Fin n)))) p.val = true
        rw [val_input]
        simp
      have hlast : z < n+gates.length := by
        by_contra! h
        have h0 : bit C (S i) z = false := val_beyond C _ h
        simp [h0] at hz
      have hW : z ∈ W := Finset.mem_image.mpr
        ⟨z-n,Finset.mem_range.mpr (by omega),by omega⟩
      by_cases hall : ∀ j, j ≠ i → bit C (S j) z = false
      · exact Or.inl (Finset.mem_filter.mpr ⟨hW,hz,hall⟩)
      · push Not at hall
        obtain ⟨j,hj,hv⟩ := hall
        exact Or.inr ⟨S j,Or.inr ⟨j,hj,rfl⟩,by simpa using hv⟩
    let E (z : ℕ) (U : Finset (Fin n)) := bit C U z = true
    have branch (z : ℕ) (hz : z ∈ G i) : Branch E T (G i) z := by
      obtain ⟨hW,hz,_⟩ := Finset.mem_filter.mp hz
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hW
      have hidx : j < C.gates.length := Finset.mem_range.mp hj
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hidx
      obtain ⟨hop,hlen⟩ := hb g (List.getElem_mem hidx)
      let D := g.inputs.toFinset.filter fun p => p < n+j ∧ bit C (S i) p = true
      have hD {p} : p ∈ D ↔ p ∈ g.inputs ∧ p < n+j ∧ bit C (S i) p = true := by simp [D]
      refine ⟨D, (Finset.card_filter_le ..).trans (g.inputs.toFinset_card_le.trans hlen), ?_, ?_⟩
      · intro p hp
        have hp' := hD.mp hp
        exact ⟨hp'.2.1, classify p hp'.2.2⟩
      · intro U hU
        exact gate_imp C hg hop (S i) U (fun p hp hp' hpt => hU p (hD.mpr ⟨hp,hp',hpt⟩)) hz
    have hroot : bit C (S i) (out i) = true :=
      (output i (S i) (by rw [hsize]; exact hqK)).mpr (by rfl)
    obtain ⟨Z,hZ,ht,hforce⟩ := frontier E T (G i) branch {out i} (by simpa using classify _ hroot)
    have hZc : Z.card ≤ c := by simp only [Finset.card_singleton] at hZ; omega
    let R (z : ℕ) : Finset (Fin n) := if h : T z then h.choose else ∅
    have hR (z : ℕ) (hz : z ∈ Z) : Allowed S i (R z) ∧ bit C (R z) z = true := by
      simpa only [R, dite_eq_left (ht z hz)] using (ht z hz).choose_spec
    let P := Z.biUnion R
    have hwP : P.card ≤ K := by
      have h1 := union_weight hq S hsize hpair i Z R fun z hz => (hR z hz).1
      have h2 := Nat.mul_le_mul_right q hZc
      dsimp [P]
      omega
    have htrue : bit C P (out i) = true := by
      apply hforce P _ (out i) (Finset.mem_singleton_self _)
      intro z hz
      exact bit_mono C hmono (fun _ hx => Finset.mem_biUnion.mpr ⟨z,hz,hx⟩) z (hR z hz).2
    have hsub := (output i P hwP).mp htrue
    have his : (P ∩ S i).card ≤ Z.card :=
      intersection_weight S hpair i Z R fun z hz => (hR z hz).1
    rw [Finset.inter_eq_right.mpr hsub, hsize] at his
    omega
  have dis : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro z hi hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have hh := hi'.2 j hij.symm
    simp [hj'.1] at hh
  calc
    m*c = ∑ _i : Fin m, c := by simp
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ => count i
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion dis).symm
    _ ≤ W.card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_filter.mp hi).1
    _ ≤ gates.length := Finset.card_image_le.trans_eq (Finset.card_range _)
