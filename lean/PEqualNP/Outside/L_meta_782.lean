import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_length (l : List Gate) (w : List Bool) :
    (l.foldl step w).length = w.length + l.length := by
  induction l generalizing w with
  | nil => simp
  | cons g l ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_getD (l : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (l.foldl step w).getD i false = w.getD i false := by
  induction l generalizing w with
  | nil => rfl
  | cons g l ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact step_getD w g i hi

theorem foldl_gate (l1 l2 : List Gate) (g : Gate) (x : List Bool) :
    ((l1 ++ g :: l2).foldl step x).getD (x.length + l1.length) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + l1.length then ((l1 ++ g :: l2).foldl step x).getD i false
        else false) := by
  rw [List.foldl_append, List.foldl_cons]
  have hlen := foldl_length l1 x
  rw [← hlen]
  generalize l1.foldl step x = W
  rw [foldl_getD l2 (step W g) W.length (by simp [step])]
  have h1 : (step W g).getD W.length false =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp [step]
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hi
  · rw [foldl_getD l2 (step W g) i (by simp [step]; omega)]
    exact (step_getD W g i hi).symm
  · exact List.getD_eq_default _ _ (by omega)

theorem foldl_gate' (gs l1 l2 : List Gate) (g : Gate) (h : gs = l1 ++ g :: l2)
    (x : List Bool) :
    (gs.foldl step x).getD (x.length + l1.length) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + l1.length then (gs.foldl step x).getD i false else false) := by
  subst h
  exact foldl_gate l1 l2 g x

def val (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def rd (C : Circuit) {n : ℕ} (x : Fin n → Bool) (t a : ℕ) : Bool :=
  if a < t then val C x a else false

theorem rd_true (C : Circuit) {n : ℕ} (x : Fin n → Bool) (t a : ℕ) :
    rd C x t a = true ↔ a < t ∧ val C x a = true := by
  unfold rd
  split_ifs with h <;> simp [h]

theorem val_input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : val C x w = false := by
  unfold val
  rw [wires_eq]
  apply List.getD_eq_default
  rw [foldl_length, List.length_ofFn]
  exact hw

theorem val_gate (C : Circuit) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => rd C x (n + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have h := foldl_gate' C.gates (C.gates.take j) (C.gates.drop (j + 1)) C.gates[j] hsplit
    (List.ofFn x)
  rw [List.length_ofFn, List.length_take, Nat.min_eq_left hj.le] at h
  exact h

theorem gate_form (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b : ℕ, (∀ x : Fin n → Bool, val C x (n + j) = (rd C x (n + j) a && rd C x (n + j) b)) ∨
      (∀ x : Fin n → Bool, val C x (n + j) = (rd C x (n + j) a || rd C x (n + j) b)) := by
  obtain ⟨hop, hlen⟩ := hg C.gates[j] (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  refine ⟨a, b, ?_⟩
  rcases hop with h | h
  · left
    intro x
    rw [val_gate C x j hj, h, hab]
    simp [GateOp.eval]
  · right
    intro x
    rw [val_gate C x j hj, h, hab]
    simp [GateOp.eval]

theorem val_mono (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ w, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hw : w < n
    · rw [val_input C y w hw]
      rw [val_input C x w hw] at hx
      exact hxy _ hx
    · by_cases hw2 : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        obtain ⟨a, b, hab | hab⟩ := gate_form C n hg j (by omega)
        · rw [hab] at hx ⊢
          rw [Bool.and_eq_true, rd_true, rd_true] at hx ⊢
          exact ⟨⟨hx.1.1, ih a hx.1.1 hx.1.2⟩, ⟨hx.2.1, ih b hx.2.1 hx.2.2⟩⟩
        · rw [hab] at hx ⊢
          rw [Bool.or_eq_true, rd_true, rd_true] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl ⟨hx.1, ih a hx.1 hx.2⟩
          · exact Or.inr ⟨hx.1, ih b hx.1 hx.2⟩
      · rw [val_big C x w (by omega)] at hx
        exact absurd hx (by simp)

def pts (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n => val C (fun q : Fin n => decide (q = p)) w = true)

theorem mem_pts (C : Circuit) (n : ℕ) (w : ℕ) (p : Fin n) :
    p ∈ pts C n w ↔ val C (fun q : Fin n => decide (q = p)) w = true := by
  simp [pts]

theorem pts_gate (C : Circuit) (n : ℕ) (w : ℕ) (h : 2 ≤ (pts C n w).card) :
    n ≤ w ∧ w < n + C.gates.length := by
  by_contra hcon
  have hle : (pts C n w).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [mem_pts] at hp hq
    by_cases hw : w < n
    · rw [val_input C _ w hw] at hp hq
      simp at hp hq
      rw [← hp, ← hq]
    · rw [val_big C _ w (by omega)] at hp
      exact absurd hp (by simp)
  omega

def Inv (C : Circuit) (n : ℕ) (o : ℕ) (F : Finset ℕ) : Prop :=
  ∀ x y : Fin n → Bool, (∀ w ∈ F, val C x w = true → val C y w = true) →
    val C x o = true → val C y o = true

def privSet (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (u : ℕ) : Finset ℕ :=
  (Finset.range u).filter (fun w => pts C n w ⊆ S ∧ 2 ≤ (pts C n w).card)

theorem frontier (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) (o : ℕ) :
    ∀ u : ℕ, ∀ F : Finset ℕ, Inv C n o F →
      (∀ w ∈ F, pts C n w ⊆ S ∧ 2 ≤ (pts C n w).card → w < u) →
      ∃ F' : Finset ℕ, Inv C n o F' ∧
        (∀ w ∈ F', ¬ (pts C n w ⊆ S ∧ 2 ≤ (pts C n w).card)) ∧
        F'.card ≤ F.card + (privSet C n S u).card := by
  intro u
  induction u with
  | zero =>
    intro F hF hlt
    exact ⟨F, hF, fun w hw hp => absurd (hlt w hw hp) (by omega), Nat.le_add_right _ _⟩
  | succ u ih =>
    intro F hF hlt
    by_cases h : u ∈ F ∧ (pts C n u ⊆ S ∧ 2 ≤ (pts C n u).card)
    · obtain ⟨huF, hpu⟩ := h
      obtain ⟨hnu, hun⟩ := pts_gate C n u hpu.2
      obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
      obtain ⟨a, b, hab⟩ := gate_form C n hg j (by omega)
      have hF1 : Inv C n o (F.erase (n + j) ∪ ({a, b} : Finset ℕ).filter (fun i => i < n + j)) := by
        intro x y hxy hx
        apply hF x y _ hx
        intro w hw hwx
        by_cases hwu : w = n + j
        · subst hwu
          have hch : ∀ i, i ∈ ({a, b} : Finset ℕ) → rd C x (n + j) i = true →
              rd C y (n + j) i = true := by
            intro i hi hri
            rw [rd_true] at hri ⊢
            refine ⟨hri.1, hxy i ?_ hri.2⟩
            exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hri.1⟩)
          rcases hab with hab | hab
          · rw [hab] at hwx ⊢
            rw [Bool.and_eq_true] at hwx ⊢
            exact ⟨hch a (by simp) hwx.1, hch b (by simp) hwx.2⟩
          · rw [hab] at hwx ⊢
            rw [Bool.or_eq_true] at hwx ⊢
            rcases hwx with hwx | hwx
            · exact Or.inl (hch a (by simp) hwx)
            · exact Or.inr (hch b (by simp) hwx)
        · exact hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwu, hw⟩)) hwx
      have hlt1 : ∀ w ∈ F.erase (n + j) ∪ ({a, b} : Finset ℕ).filter (fun i => i < n + j),
          pts C n w ⊆ S ∧ 2 ≤ (pts C n w).card → w < n + j := by
        intro w hw hp
        rcases Finset.mem_union.mp hw with hw | hw
        · have h1 := Finset.mem_erase.mp hw
          have h2 := hlt w h1.2 hp
          have h3 := h1.1
          omega
        · exact (Finset.mem_filter.mp hw).2
      obtain ⟨F', hF', hnp, hcard⟩ := ih _ hF1 hlt1
      refine ⟨F', hF', hnp, ?_⟩
      have hc1 : (F.erase (n + j) ∪ ({a, b} : Finset ℕ).filter (fun i => i < n + j)).card
          ≤ F.card + 1 := by
        have e1 := Finset.card_union_le (F.erase (n + j))
          (({a, b} : Finset ℕ).filter (fun i => i < n + j))
        have e2 := Finset.card_erase_of_mem huF
        have e3 := Finset.card_filter_le ({a, b} : Finset ℕ) (fun i => i < n + j)
        have e4 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        have e5 : 0 < F.card := Finset.card_pos.mpr ⟨_, huF⟩
        omega
      have hc2 : (privSet C n S (n + j + 1)).card = (privSet C n S (n + j)).card + 1 := by
        unfold privSet
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hpu]
        rw [Finset.card_insert_of_notMem]
        simp
      omega
    · have hlt1 : ∀ w ∈ F, pts C n w ⊆ S ∧ 2 ≤ (pts C n w).card → w < u := by
        intro w hw hp
        have h2 := hlt w hw hp
        have h3 : w ≠ u := by
          rintro rfl
          exact h ⟨hw, hp⟩
        omega
      obtain ⟨F', hF', hnp, hcard⟩ := ih F hF hlt1
      refine ⟨F', hF', hnp, ?_⟩
      have hc2 : (privSet C n S u).card ≤ (privSet C n S (u + 1)).card := by
        unfold privSet
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        exact Finset.range_mono (Nat.le_succ u)
      omega

theorem main (n k c o : ℕ) (S : Finset (Fin n)) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h2 : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val C x o = false)
    (hck : c ≤ k) (hcS : c + 1 ≤ (pts C n o).card) :
    c ≤ ((Finset.range C.gates.length).filter (fun j => pts C n (n + j) ⊆ S ∧
      2 ≤ (pts C n (n + j)).card)).card := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨F, hInv, hnp, hcard⟩ := frontier C n hg S o (o + 1) {o}
    (fun x y h hx => h o (Finset.mem_singleton_self o) hx)
    (fun w hw _ => by rw [Finset.mem_singleton] at hw; omega)
  have hm : (privSet C n S (o + 1)).card ≤ ((Finset.range C.gates.length).filter
      (fun j => pts C n (n + j) ⊆ S ∧ 2 ≤ (pts C n (n + j)).card)).card := by
    apply Finset.card_le_card_of_injOn (fun w => w - n)
    · intro w hw
      have hw' := (Finset.mem_filter.mp hw).2
      have hgw := pts_gate C n w hw'.2
      have e : n + (w - n) = w := by omega
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      rw [e]
      exact ⟨by omega, hw'⟩
    · intro w1 hw1 w2 hw2 he
      have hg1 := pts_gate C n w1 (Finset.mem_filter.mp hw1).2.2
      have hg2 := pts_gate C n w2 (Finset.mem_filter.mp hw2).2.2
      simp only at he
      omega
  have hFc : F.card ≤ c := by
    rw [Finset.card_singleton] at hcard
    omega
  have hSne : (pts C n o).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p0, _⟩ := hSne
  have hne : Nonempty (Fin n) := ⟨p0⟩
  have hex : ∀ w : ℕ, ¬ pts C n w ⊆ S → ∃ p, p ∈ pts C n w ∧ p ∉ S := fun w hw =>
    Finset.not_subset.mp hw
  choose! pt hpt using hex
  have hmonoQ : ∀ w ∈ F, ¬ pts C n w ⊆ S →
      val C (fun q : Fin n => decide (q ∈ (F.filter (fun w => ¬ pts C n w ⊆ S)).image pt)) w
        = true := by
    intro w hw hl
    have hv := (mem_pts C n w (pt w)).mp (hpt w hl).1
    apply val_mono C n hg _ _ _ w hv
    intro q hq
    have hq' : q = pt w := by simpa using hq
    rw [hq']
    simp only [decide_eq_true_eq]
    exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hl⟩, rfl⟩
  have h0 : val C (fun q : Fin n => decide (q ∈ (F.filter (fun w => ¬ pts C n w ⊆ S)).image pt)) o
      = false := by
    apply h2
    · have e : (Finset.univ.filter (fun q : Fin n =>
          decide (q ∈ (F.filter (fun w => ¬ pts C n w ⊆ S)).image pt) = true))
          = (F.filter (fun w => ¬ pts C n w ⊆ S)).image pt := by
        ext q
        simp
      rw [e]
      have e1 := Finset.card_image_le (s := F.filter (fun w => ¬ pts C n w ⊆ S)) (f := pt)
      have e2 := Finset.card_filter_le F (fun w => ¬ pts C n w ⊆ S)
      omega
    · intro q hq
      simp only [decide_eq_false_iff_not]
      intro hqQ
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hqQ
      exact (hpt w (Finset.mem_filter.mp hw).2).2 hq
  have hwit : ∀ p ∈ pts C n o, ∃ w, w ∈ F ∧ p ∈ pts C n w ∧ (pts C n w).card ≤ 1 := by
    intro p hp
    have hp1 := (mem_pts C n o p).mp hp
    by_contra hcon
    push_neg at hcon
    have hall : ∀ w ∈ F, val C (fun q : Fin n => decide (q = p)) w = true →
        val C (fun q : Fin n => decide (q ∈ (F.filter (fun w => ¬ pts C n w ⊆ S)).image pt)) w
          = true := by
      intro w hw hwp
      by_contra hne'
      have hsub : pts C n w ⊆ S := by
        by_contra hl
        exact hne' (hmonoQ w hw hl)
      have hcw := hcon w hw ((mem_pts C n w p).mpr hwp)
      exact hnp w hw ⟨hsub, by omega⟩
    have := hInv _ _ hall hp1
    rw [h0] at this
    exact absurd this (by simp)
  choose! f hf using hwit
  have hSF : (pts C n o).card ≤ F.card := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      exact (hf p hp).1
    · intro p hp p' hp' he
      have hp'' : p' ∈ pts C n (f p) := by
        rw [he]
        exact (hf p' hp').2.1
      exact Finset.card_le_one.mp (hf p hp).2.2 p (hf p hp).2.1 p' hp''
  omega

theorem total (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (c : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hprom : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → val C x (o i) = false)
    (hck : ∀ i : Fin m, c i ≤ k)
    (hcL : ∀ i : Fin m, c i + 1 ≤ (pts C n (o i)).card) :
    ∑ i : Fin m, c i ≤ C.gates.length := by
  classical
  let P : Fin m → Finset ℕ := fun i => (Finset.range C.gates.length).filter
    (fun j => pts C n (n + j) ⊆ S i ∧ 2 ≤ (pts C n (n + j)).card)
  have h1 : ∀ i, c i ≤ (P i).card := fun i =>
    main n k (c i) (o i) (S i) C hg (hprom i) (hck i) (hcL i)
  have hdis : ∀ i j : Fin m, i ≠ j → Disjoint (P i) (P j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro t hti htj
    have hi := (Finset.mem_filter.mp hti).2
    have hj := (Finset.mem_filter.mp htj).2
    have hsub : pts C n (n + t) ⊆ S i ∩ S j := Finset.subset_inter hi.1 hj.1
    have e1 := Finset.card_le_card hsub
    have e2 := hS i j hij
    omega
  have hunion : (Finset.univ.biUnion P).card = ∑ i : Fin m, (P i).card :=
    Finset.card_biUnion (fun i _ j _ hij => hdis i j hij)
  have hsub : Finset.univ.biUnion P ⊆ Finset.range C.gates.length := by
    intro t ht
    obtain ⟨i, _, hti⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_of_mem_filter t hti
  have hle := Finset.card_le_card hsub
  rw [Finset.card_range] at hle
  calc ∑ i : Fin m, c i ≤ ∑ i : Fin m, (P i).card := Finset.sum_le_sum (fun i _ => h1 i)
    _ = (Finset.univ.biUnion P).card := hunion.symm
    _ ≤ C.gates.length := hle

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS _ hg _ hprom hck hcL
  exact PEqualNP.Outside.L_meta_782.total n m k S C o c hS hg hprom hck hcL
