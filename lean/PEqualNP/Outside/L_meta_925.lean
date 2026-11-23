import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_925

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
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


private lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ r ∈ l, f r = true → g r = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro hf r hr
    exact h r hr (hf r hr)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨r, hr, hf⟩
    exact ⟨r, hr, h r hr hf⟩

private lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · rw [gate_value C x w (by omega) hw, gate_value C y w (by omega) hw]
      apply eval_mono _ (hG _ (List.getElem_mem _))
      intro r _ hr
      by_cases hrw : r < w
      · simp only [hrw, ite_true] at hr ⊢
        exact ih r hrw hr
      · simp [hrw] at hr
    · simp [missing_value C x w (by omega)]

private lemma children {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : Fin n → Bool) (t : ℕ) (hn : n ≤ t) (ht : t < n + C.size) (hz : value C z t = true) :
    ∃ D : Finset ℕ, D.card ≤ 2 ∧ (∀ r ∈ D, r < t ∧ value C z r = true) ∧
      ∀ x : Fin n → Bool, value C x t = false → ∃ r ∈ D, value C x r = false := by
  have formula := fun (y : Fin n → Bool) => gate_value C y t hn ht
  simp only at formula
  set g := C.gates[t - n]'(by unfold Circuit.size at ht; omega) with hg
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  rw [formula z] at hz
  rcases hop with hop | hop
  · refine ⟨g.inputs.toFinset.filter (· < t), ?_, ?_, ?_⟩
    · exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
    · intro r hr
      obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
      have hr1 := List.mem_toFinset.mp hr1
      refine ⟨hr2, ?_⟩
      rw [hop] at hz
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at hz
      simpa [hr2] using hz r hr1
    · intro x hx
      rw [formula x, hop] at hx
      rw [hop] at hz
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at hz
      simp only [GateOp.eval] at hx
      obtain ⟨r, hr, hrx⟩ : ∃ r ∈ g.inputs, (if r < t then value C x r else false) = false := by
        by_contra hne
        simp only [not_exists, not_and, Bool.not_eq_false] at hne
        have hall : (g.inputs.map fun r => if r < t then value C x r else false).all id = true := by
          simp only [List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂]
          exact hne
        rw [hall] at hx
        exact absurd hx (by simp)
      by_cases hrt : r < t
      · exact ⟨r, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hrt⟩, by simpa [hrt] using hrx⟩
      · have := hz r hr
        simp [hrt] at this
  · rw [hop] at hz
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and] at hz
    obtain ⟨r, hr, hrz⟩ := hz
    have hrt : r < t := by
      by_contra h
      simp [h] at hrz
    refine ⟨{r}, by simp, ?_, ?_⟩
    · intro r' hr'
      rw [Finset.mem_singleton.mp hr']
      exact ⟨hrt, by simpa [hrt] using hrz⟩
    · intro x hx
      rw [formula x, hop] at hx
      simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂] at hx
      refine ⟨r, Finset.mem_singleton_self r, ?_⟩
      have := hx r hr
      simpa [hrt] using this

private def ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun p => decide (p ∈ A)

private def spec {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter
    (fun t => value C (ind (S w)) t = true ∧ ∀ v, v ≠ w → value C (ind (S v)) t = false)

private def Inv {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (K : ℕ) (w : Fin m)
    (F : Finset ℕ) (P : Finset (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
    (∀ p ∈ P, x p = true) → (∃ p ∈ S w, x p = false) → ∃ r ∈ F, value C x r = false

private def PInv {n m : ℕ} (q : ℕ) (S : Fin m → Finset (Fin n)) (w : Fin m)
    (P : Finset (Fin n)) (d : ℕ) : Prop :=
  P.card ≤ d * q + 1 ∧ (P ∩ S w).card ≤ d ∧ (P = ∅ ∨ ∃ v, S v ⊆ P)

private lemma pinv_step {n m : ℕ} (q : ℕ) (S : Fin m → Finset (Fin n))
    (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (w v : Fin m) (hv : v ≠ w) (P : Finset (Fin n)) (d : ℕ) (hP : PInv q S w P d) :
    PInv q S w (P ∪ S v) (d + 1) := by
  classical
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, Or.inr ⟨v, Finset.subset_union_right⟩⟩
  · rcases h3 with h3 | ⟨v0, hv0⟩
    · subst h3
      simp [hcard v]
      nlinarith
    · have hu : P ∪ S v = P ∪ (S v \ P) := by
        ext a; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
      have hsd : (S v \ P).card ≤ q := by
        have hsub : S v \ P ⊆ S v \ S v0 := Finset.sdiff_subset_sdiff (le_refl _) hv0
        refine (Finset.card_le_card hsub).trans ?_
        have he := Finset.card_sdiff_add_card_inter (S v) (S v0)
        by_cases hvv : v = v0
        · subst hvv
          simp
        · have := hint v v0 hvv
          rw [hcard v, this] at he
          omega
      rw [hu]
      have := Finset.card_union_le P (S v \ P)
      nlinarith
  · have hsub : (P ∪ S v) ∩ S w ⊆ (P ∩ S w) ∪ (S v ∩ S w) := by
      intro a; simp only [Finset.mem_union, Finset.mem_inter]; tauto
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [hint v w hv] at this
    omega

private lemma descend {n m : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (q K c : ℕ) (S : Fin m → Finset (Fin n))
    (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (w : Fin m) (t : ℕ) :
    ∀ (F : Finset ℕ) (P : Finset (Fin n)) (d : ℕ), Inv C S K w F P →
      (∀ r ∈ F, value C (ind (S w)) r = true) → (∀ r ∈ F, n ≤ r → r < t) → PInv q S w P d →
      F.card + d + ((spec C S w).filter (· < t)).card ≤ c →
      ∃ (F' : Finset ℕ) (P' : Finset (Fin n)) (d' : ℕ), Inv C S K w F' P' ∧
        (∀ r ∈ F', r < n) ∧ PInv q S w P' d' ∧ F'.card + d' ≤ c := by
  classical
  have hG' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hG g hg).1
  induction t with
  | zero =>
    intro F P d hI _ hlt hP hc
    refine ⟨F, P, d, hI, fun r hr => ?_, hP, by omega⟩
    by_contra h
    have := hlt r hr (by omega)
    omega
  | succ t ih =>
    intro F P d hI htrue hlt hP hc
    have hle : ((spec C S w).filter (· < t)).card ≤ ((spec C S w).filter (· < t + 1)).card :=
      Finset.card_le_card fun r hr =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1,
          by have := (Finset.mem_filter.mp hr).2; omega⟩
    by_cases htF : t ∈ F ∧ n ≤ t
    · have htsz : t < n + C.size := by
        by_contra h
        have := htrue t htF.1
        rw [missing_value C _ t (by omega)] at this
        exact Bool.false_ne_true this
      have hFpos : 1 ≤ F.card := Finset.card_pos.mpr ⟨t, htF.1⟩
      have hecard := Finset.card_erase_add_one htF.1
      by_cases hspec : ∀ v, v ≠ w → value C (ind (S v)) t = false
      · have hmem : t ∈ spec C S w :=
          Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨htF.2, htsz⟩, htrue t htF.1, hspec⟩
        have hfilter : (spec C S w).filter (· < t + 1) =
            insert t ((spec C S w).filter (· < t)) := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hlt⟩
            by_cases h : r = t
            · exact Or.inl h
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, hlt⟩)
            · exact ⟨hmem, by omega⟩
            · exact ⟨hg, by omega⟩
        rw [hfilter, Finset.card_insert_of_notMem (by simp)] at hc
        obtain ⟨D, hDc, hDt, hDx⟩ :=
          children C hG (ind (S w)) t htF.2 htsz (htrue t htF.1)
        have hFc := Finset.card_union_le (F.erase t) D
        apply ih (F.erase t ∪ D) P d
        · intro x hx hPx hmiss
          obtain ⟨r, hr, hrx⟩ := hI x hx hPx hmiss
          by_cases hrt : r = t
          · subst hrt
            obtain ⟨r', hr', hr'x⟩ := hDx x hrx
            exact ⟨r', Finset.mem_union_right _ hr', hr'x⟩
          · exact ⟨r, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hrt, hr⟩), hrx⟩
        · intro r hr
          rcases Finset.mem_union.mp hr with hr | hr
          · exact htrue r (Finset.mem_erase.mp hr).2
          · exact (hDt r hr).2
        · intro r hr hnr
          rcases Finset.mem_union.mp hr with hr | hr
          · have hne := (Finset.mem_erase.mp hr).1
            have := hlt r (Finset.mem_erase.mp hr).2 hnr
            omega
          · exact (hDt r hr).1
        · exact hP
        · omega
      · push Not at hspec
        obtain ⟨v, hvw, hvt⟩ := hspec
        apply ih (F.erase t) (P ∪ S v) (d + 1)
        · intro x hx hPx hmiss
          obtain ⟨r, hr, hrx⟩ := hI x hx (fun p hp => hPx p (Finset.mem_union_left _ hp)) hmiss
          by_cases hrt : r = t
          · subst hrt
            have := value_mono C hG' (ind (S v)) x (fun p hp => by
              apply hPx p (Finset.mem_union_right _ _)
              simpa [ind] using hp) r (by simpa using hvt)
            rw [hrx] at this
            exact absurd this Bool.false_ne_true
          · exact ⟨r, Finset.mem_erase.mpr ⟨hrt, hr⟩, hrx⟩
        · intro r hr
          exact htrue r (Finset.mem_erase.mp hr).2
        · intro r hr hnr
          have hne := (Finset.mem_erase.mp hr).1
          have := hlt r (Finset.mem_erase.mp hr).2 hnr
          omega
        · exact pinv_step q S hcard hint w v hvw P d hP
        · omega
    · apply ih F P d hI htrue
      · intro r hr hnr
        have := hlt r hr hnr
        have hne : r ≠ t := fun e => htF ⟨e ▸ hr, e ▸ hnr⟩
        omega
      · exact hP
      · omega

private lemma spec_card {n m : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (q K c : ℕ) (S : Fin m → Finset (Fin n))
    (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (o : ℕ) (w : Fin m)
    (hout : ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
      value C x o = decide (∀ v ∈ S w, x v = true))
    (hq : 1 ≤ q) (hcq : c ≤ q) (hcK : c * q < K) : c ≤ (spec C S w).card := by
  classical
  by_contra hlt
  push Not at hlt
  have hc1 : 1 ≤ c := by omega
  have hqK : q + 1 ≤ K := by nlinarith
  have hwt : (Finset.univ.filter (fun i : Fin n => ind (S w) i = true)).card ≤ K := by
    have : Finset.univ.filter (fun i : Fin n => ind (S w) i = true) = S w := by
      ext p; simp [ind]
    rw [this, hcard w]
    exact hqK
  have ho : value C (ind (S w)) o = true := by
    rw [hout _ hwt]
    simp [ind]
  have hI0 : Inv C S K w {o} ∅ := by
    intro x hx _ hmiss
    refine ⟨o, Finset.mem_singleton_self o, ?_⟩
    rw [hout x hx]
    obtain ⟨p, hp, hpx⟩ := hmiss
    simp only [decide_eq_false_iff_not, not_forall]
    exact ⟨p, hp, by simp [hpx]⟩
  have hosz : n ≤ o → o < n + C.size := by
    intro _
    by_contra h
    rw [missing_value C _ o (by omega)] at ho
    exact Bool.false_ne_true ho
  have hPI : PInv q S w ∅ 0 := ⟨by simp, by simp, Or.inl rfl⟩
  have hfl : ((spec C S w).filter (· < n + C.size)).card ≤ (spec C S w).card :=
    Finset.card_filter_le _ _
  obtain ⟨F, P, d, hI, hFn, ⟨hP1, hP2, _⟩, hFd⟩ :=
    descend C hG q K c S hcard hint w (n + C.size) {o} ∅ 0 hI0
      (fun r hr => by rw [Finset.mem_singleton.mp hr]; exact ho)
      (fun r hr hnr => by rw [Finset.mem_singleton.mp hr] at hnr ⊢; exact hosz hnr)
      hPI (by simp; omega)
  let Fp : Finset (Fin n) := Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ F)
  have hFp : Fp.card ≤ F.card :=
    Finset.card_le_card_of_injOn (fun p : Fin n => (p : ℕ))
      (fun p hp => (Finset.mem_filter.mp hp).2) (fun a _ b _ h => Fin.ext h)
  let X := P ∪ Fp
  have hX : X.card ≤ K := by
    show (P ∪ Fp).card ≤ K
    have h1 := Finset.card_union_le P Fp
    have h2 : d * q + F.card ≤ c * q := by
      have := Nat.mul_le_mul_right q hFd
      nlinarith
    omega
  have hXw : (X ∩ S w).card < (S w).card := by
    have hsub : X ∩ S w ⊆ (P ∩ S w) ∪ Fp := by
      intro a; simp only [X, Finset.mem_union, Finset.mem_inter]; tauto
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [hcard w]
    omega
  obtain ⟨p, hp, hpX⟩ := Finset.exists_mem_notMem_of_card_lt_card hXw
  have hpX' : p ∉ X := fun h => hpX (Finset.mem_inter.mpr ⟨h, hp⟩)
  obtain ⟨r, hr, hrx⟩ := hI (ind X)
    (by
      have : Finset.univ.filter (fun i : Fin n => ind X i = true) = X := by ext a; simp [ind]
      rw [this]; exact hX)
    (fun a ha => by simp [ind, X, ha])
    ⟨p, hp, by simp [ind, hpX']⟩
  have hrn := hFn r hr
  have hv := input_value C (ind X) ⟨r, hrn⟩
  simp only at hv
  rw [hv] at hrx
  have : (⟨r, hrn⟩ : Fin n) ∈ X := Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨by simp, hr⟩)
  simp [ind, this] at hrx

end PEqualNP.Outside.L_meta_925

open PEqualNP.Outside.L_meta_925 in
theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hcard hint gates out hG hout c hcq hcK
  let C : Circuit := ⟨gates, 0⟩
  have hGC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := hG
  have hspec : ∀ w, c ≤ (spec C S w).card := by
    intro w
    apply spec_card C hGC q K c S hcard hint (out w) w _ (by omega) hcq hcK
    intro x hx
    exact hout w x hx
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint (spec C S) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun t hti htj => ?_
    have hi := (Finset.mem_filter.mp hti).2
    have hj := (Finset.mem_filter.mp htj).2
    have := hi.2 j (Ne.symm hij)
    rw [hj.1] at this
    exact Bool.false_ne_true this.symm
  calc
    m * c = ∑ _w : Fin m, c := by simp
    _ ≤ ∑ w : Fin m, (spec C S w).card := Finset.sum_le_sum fun w _ => hspec w
    _ = (Finset.univ.biUnion (spec C S)).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun t ht => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ht
      exact (Finset.mem_filter.mp hi).1
    _ = gates.length := by simp [C, Circuit.size]
