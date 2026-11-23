import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1375

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

abbrev good (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma value_mono {n : ℕ} (C : Circuit) (hG : good C)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · intro hx
      have hfx := gate_value C x w (by omega) hw
      have hfy := gate_value C y w (by omega) hw
      rw [hfx] at hx
      rw [hfy]
      obtain ⟨hop, _⟩ := hG (C.gates[w - n]'(by unfold Circuit.size at hw; omega)) (List.getElem_mem _)
      rcases hop with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
        rintro b ⟨r, hr, rfl⟩
        by_cases hrt : r < w
        · simpa [hrt] using ih r hrt (by simpa [hrt] using hx _ ⟨r, hr, rfl⟩)
        · have := hx _ ⟨r, hr, rfl⟩
          simp [hrt] at this
      · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
        obtain ⟨_, ⟨r, hr, rfl⟩, hv⟩ := hx
        by_cases hrt : r < w
        · exact ⟨_, ⟨r, hr, rfl⟩, by simpa [hrt] using ih r hrt (by simpa [hrt] using hv)⟩
        · simp [hrt] at hv
    · simp [missing_value C x w (by omega)]

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

def bit {n : ℕ} (A : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ A)

lemma smart_cut {n : ℕ} (C : Circuit) (hG : good C)
    (S : Finset (Fin n)) (y : Fin n → Bool)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hitAnd : Bool)
    (hFt : ∀ w ∈ F, w ∈ G → w < t)
    (hFy : ∀ w ∈ F, value C y w = false)
    (hFsub : hitAnd = false → ∀ w ∈ F, support C w ⊆ S) :
    ∃ (B : Finset ℕ) (hit' : Bool),
      Disjoint B G ∧
      (∀ w ∈ B, value C y w = false) ∧
      (hit' = false → ∀ w ∈ B, support C w ⊆ S) ∧
      B.card + (if hit' then 1 else 0) ≤
        F.card + (if hitAnd then 1 else 0) + (G.filter (· < t)).card ∧
      ∀ p : Fin n, (∃ w ∈ F, value C (fun q => decide (q = p)) w = true) →
        ∃ w ∈ B, value C (fun q => decide (q = p)) w = true := by
  classical
  induction t generalizing F hitAnd with
  | zero =>
    refine ⟨F, hitAnd, Finset.disjoint_left.mpr (fun w hw hg => by have := hFt w hw hg; omega),
      hFy, hFsub, by simp, fun _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · have htg := hGates t hex.2
      have htlen : t - n < C.size := by omega
      let g := C.gates[t - n]'(by simpa [Circuit.size] using htlen)
      have hty : value C y t = false := hFy t hex.1
      have hgval : ∀ x : Fin n → Bool,
          value C x t = g.op.eval (g.inputs.map fun r => if r < t then value C x r else false) :=
        fun x => gate_value C x t htg.1 htg.2
      have hfilt_eq : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      have hfilt_card : (G.filter (· < t + 1)).card = (G.filter (· < t)).card + 1 := by
        rw [hfilt_eq, Finset.card_insert_of_notMem (by simp)]
      obtain ⟨hop, hlen2⟩ := hG g (List.getElem_mem _)
      rcases hop with hop | hop
      · have hgy : (g.inputs.map fun r => if r < t then value C y r else false).all id = false := by
          have h := (hgval y).symm
          rw [hty, hop] at h
          exact h
        have hgy' : ¬ ((g.inputs.map fun r => if r < t then value C y r else false).all id = true) :=
          fun h => Bool.false_ne_true (hgy.symm.trans h)
        simp only [List.all_eq_true, List.mem_map, id_eq, not_forall] at hgy'
        obtain ⟨_, ⟨u, hu, rfl⟩, huf⟩ := hgy'
        by_cases hut : u < t
        · have huy : value C y u = false := by
            simp only [hut, ↓reduceIte] at huf
            exact Bool.eq_false_iff.mpr huf
          let F' := insert u (F.erase t)
          have hF't : ∀ w ∈ F', w ∈ G → w < t := by
            intro w hw hg
            rcases Finset.mem_insert.mp hw with rfl | hw'
            · exact hut
            · have hne := (Finset.mem_erase.mp hw').1
              have hlt := hFt w (Finset.mem_erase.mp hw').2 hg
              omega
          have hF'y : ∀ w ∈ F', value C y w = false := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw'
            · exact huy
            · exact hFy w (Finset.mem_erase.mp hw').2
          obtain ⟨B, hit', hdisj, hBy, hBsub, hBcard, hBcov⟩ :=
            ih F' true hF't hF'y (fun h => absurd h Bool.false_ne_true.symm)
          refine ⟨B, hit', hdisj, hBy, hBsub, ?_, ?_⟩
          · have he := Finset.card_erase_add_one hex.1
            have hi := Finset.card_insert_le u (F.erase t)
            change F'.card ≤ _ at hi
            cases hitAnd <;> simp only [↓reduceIte, Bool.false_eq_true] at hBcard ⊢ <;> omega
          · intro p ⟨w, hw, hwp⟩
            apply hBcov p
            by_cases hwt : w = t
            · subst hwt
              have hgp : (g.inputs.map fun r => if r < w then value C (fun q => decide (q = p)) r else false).all id = true := by
                have h := (hgval (fun q => decide (q = p))).symm
                rw [hwp, hop] at h
                exact h
              simp only [List.all_eq_true, List.mem_map, id_eq] at hgp
              have := hgp _ ⟨u, hu, rfl⟩
              exact ⟨u, Finset.mem_insert_self u _, by simpa [hut] using this⟩
            · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwt, hw⟩), hwp⟩
        · have hfalse : ∀ x : Fin n → Bool, value C x t = false := by
            intro x
            have hgx := hgval x
            rw [hgx, hop]
            simp only [GateOp.eval]
            rw [Bool.eq_false_iff]
            intro hall
            rw [List.all_eq_true] at hall
            have := hall (if u < t then value C x u else false) (List.mem_map_of_mem hu)
            simp [hut] at this
          let F' := F.erase t
          have hF't : ∀ w ∈ F', w ∈ G → w < t := by
            intro w hw hg
            have hne := (Finset.mem_erase.mp hw).1
            have hlt := hFt w (Finset.mem_erase.mp hw).2 hg
            omega
          obtain ⟨B, hit', hdisj, hBy, hBsub, hBcard, hBcov⟩ :=
            ih F' true hF't (fun w hw => hFy w (Finset.mem_erase.mp hw).2)
              (fun h => absurd h Bool.false_ne_true.symm)
          refine ⟨B, hit', hdisj, hBy, hBsub, ?_, ?_⟩
          · have he : F'.card + 1 = F.card := Finset.card_erase_add_one hex.1
            cases hitAnd <;> simp only [↓reduceIte, Bool.false_eq_true] at hBcard ⊢ <;> omega
          · intro p ⟨w, hw, hwp⟩
            apply hBcov p
            by_cases hwt : w = t
            · subst hwt
              rw [hfalse] at hwp
              exact absurd hwp Bool.false_ne_true
            · exact ⟨w, Finset.mem_erase.mpr ⟨hwt, hw⟩, hwp⟩
      · let P := g.inputs.toFinset.filter (· < t)
        have hPcard : P.card ≤ 2 :=
          (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen2)
        let F' := F.erase t ∪ P
        have hF't : ∀ w ∈ F', w ∈ G → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw' | hw'
          · have hne := (Finset.mem_erase.mp hw').1
            have hlt := hFt w (Finset.mem_erase.mp hw').2 hg
            omega
          · exact (Finset.mem_filter.mp hw').2
        have hF'y : ∀ w ∈ F', value C y w = false := by
          intro w hw
          rcases Finset.mem_union.mp hw with hw' | hw'
          · exact hFy w (Finset.mem_erase.mp hw').2
          · have hmem := List.mem_toFinset.mp (Finset.mem_filter.mp hw').1
            have hlt := (Finset.mem_filter.mp hw').2
            have hgy : (g.inputs.map fun r => if r < t then value C y r else false).any id = false := by
              have h := (hgval y).symm
              rw [hty, hop] at h
              exact h
            have hgy' : ¬ ((g.inputs.map fun r => if r < t then value C y r else false).any id = true) :=
              fun h => Bool.false_ne_true (hgy.symm.trans h)
            simp only [List.any_eq_true, List.mem_map, id_eq] at hgy'
            rw [Bool.eq_false_iff]
            intro hv
            exact hgy' ⟨true, ⟨w, hmem, by simp [hlt, hv]⟩, rfl⟩
        have hF'sub : hitAnd = false → ∀ w ∈ F', support C w ⊆ S := by
          intro hf w hw
          rcases Finset.mem_union.mp hw with hw' | hw'
          · exact hFsub hf w (Finset.mem_erase.mp hw').2
          · intro p hp
            apply hFsub hf t hex.1
            rw [mem_support, hgval, hop]
            have hmem := List.mem_toFinset.mp (Finset.mem_filter.mp hw').1
            have hlt := (Finset.mem_filter.mp hw').2
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
            exact ⟨true, ⟨w, hmem, by simp [hlt, (mem_support C w p).mp hp]⟩, rfl⟩
        obtain ⟨B, hit', hdisj, hBy, hBsub, hBcard, hBcov⟩ :=
          ih F' hitAnd hF't hF'y hF'sub
        refine ⟨B, hit', hdisj, hBy, hBsub, ?_, ?_⟩
        · have hu := Finset.card_union_le (F.erase t) P
          have he := Finset.card_erase_add_one hex.1
          change F'.card ≤ _ at hu
          omega
        · intro p ⟨w, hw, hwp⟩
          apply hBcov p
          by_cases hwt : w = t
          · subst hwt
            have hgp : (g.inputs.map fun r => if r < w then value C (fun q => decide (q = p)) r else false).any id = true := by
              have h := (hgval (fun q => decide (q = p))).symm
              rw [hwp, hop] at h
              exact h
            simp only [List.any_eq_true, List.mem_map, id_eq] at hgp
            obtain ⟨_, ⟨u, hu, rfl⟩, huv⟩ := hgp
            by_cases hut : u < w
            · exact ⟨u, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu, hut⟩),
                by simpa [hut] using huv⟩
            · simp [hut] at huv
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩), hwp⟩
    · have hF't : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hFt w hw hg
        omega
      obtain ⟨B, hit', hdisj, hBy, hBsub, hBcard, hBcov⟩ := ih F hitAnd hF't hFy hFsub
      have hfilt_le : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card (fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩)
      exact ⟨B, hit', hdisj, hBy, hBsub, by omega, hBcov⟩

def owned {n : ℕ} (C : Circuit) (U S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    (support C w ∩ U ⊆ S ∧ 2 ≤ (support C w ∩ U).card) ∨
    (support C w ⊆ S ∧ 2 ≤ (support (n := n) C w).card)

lemma count_eq_R {n : ℕ} (C : Circuit) (hG : good C)
    (U S : Finset (Fin n)) (o : ℕ)
    (hsupp : support C o = S) (hneg : value C (bit (Finset.univ \ S)) o = false) :
    S.card - 1 ≤ (owned C U S).card := by
  classical
  let G := owned C U S
  have hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size :=
    fun w hw => Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have ho_lt : ∀ w ∈ ({o} : Finset ℕ), w ∈ G → w < n + C.size :=
    fun w _ hw => (hGates w hw).2
  obtain ⟨B, hit', hdisj, hBy, _, hBcard, hBcov⟩ :=
    smart_cut C hG S (bit (Finset.univ \ S)) G hGates (n + C.size) {o} false ho_lt
      (by intro w hw; rw [Finset.mem_singleton.mp hw]; exact hneg)
      (by intro _ w hw; rw [Finset.mem_singleton.mp hw, hsupp])
  have hsmall : ∀ w ∈ B, (support (n := n) C w).card ≤ 1 := by
    intro w hw
    have hsub : support C w ⊆ S := by
      intro p hp
      by_contra hpS
      have hpt := (mem_support C w p).mp hp
      have hmono := value_mono C hG (fun q => decide (q = p)) (bit (Finset.univ \ S)) (by
        intro q hq
        have eq : q = p := of_decide_eq_true hq
        subst q
        simp [bit, hpS]) w hpt
      rw [hBy w hw] at hmono
      exact Bool.false_ne_true hmono
    by_contra! hlarge
    have hwg := support_gate C w (by omega)
    have hwG : w ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hwg, Or.inr ⟨hsub, by omega⟩⟩
    exact Finset.disjoint_left.mp hdisj hw hwG
  have hcov : S ⊆ B.biUnion (support C) := by
    intro p hp
    have hpo : value C (fun q => decide (q = p)) o = true := (mem_support C o p).mp (hsupp.symm ▸ hp)
    obtain ⟨w, hwB, hwp⟩ := hBcov p ⟨o, Finset.mem_singleton_self o, hpo⟩
    exact Finset.mem_biUnion.mpr ⟨w, hwB, (mem_support C w p).mpr hwp⟩
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_biUnion_le_card_mul B (support C) 1 hsmall
  have h3 := Finset.card_filter_le G (· < n + C.size)
  simp only [Finset.card_singleton, Bool.false_eq_true, ↓reduceIte] at hBcard
  change _ ≤ G.card
  cases hit' <;> simp only [↓reduceIte, Bool.false_eq_true] at hBcard <;> omega

lemma count_general {n : ℕ} (C : Circuit) (hG : good C)
    (R S : Finset (Fin n)) (o : ℕ)
    (hsupp : support C o = S) (hneg : value C (bit ((Finset.univ \ R) \ S)) o = false) :
    (S \ R).card - (if (S ∩ R).Nonempty then 0 else 1) ≤ (owned C (Finset.univ \ R) S).card := by
  classical
  let U := Finset.univ \ R
  let G := owned C U S
  have hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size :=
    fun w hw => Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have ho_lt : ∀ w ∈ ({o} : Finset ℕ), w ∈ G → w < n + C.size :=
    fun w _ hw => (hGates w hw).2
  obtain ⟨B, hit', hdisj, hBy, hBsub, hBcard, hBcov⟩ :=
    smart_cut C hG S (bit (U \ S)) G hGates (n + C.size) {o} false ho_lt
      (by intro w hw; rw [Finset.mem_singleton.mp hw]; exact hneg)
      (by intro _ w hw; rw [Finset.mem_singleton.mp hw, hsupp])
  have hsmallU : ∀ w ∈ B, (support C w ∩ U).card ≤ 1 := by
    intro w hw
    have hsub : support C w ∩ U ⊆ S := by
      intro p hp
      by_contra hpS
      have hpt := (mem_support C w p).mp (Finset.mem_inter.mp hp).1
      have hpU := (Finset.mem_inter.mp hp).2
      have hmono := value_mono C hG (fun q => decide (q = p)) (bit (U \ S)) (by
        intro q hq
        have eq : q = p := of_decide_eq_true hq
        subst q
        simp [bit, hpU, hpS]) w hpt
      rw [hBy w hw] at hmono
      exact Bool.false_ne_true hmono
    by_contra! hlarge
    have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := support C w) (s₂ := U))
    have hwg := support_gate C w (by omega)
    have hwG : w ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hwg, Or.inl ⟨hsub, by omega⟩⟩
    exact Finset.disjoint_left.mp hdisj hw hwG
  have hcovU : S \ R ⊆ B.biUnion (fun w => support C w ∩ U) := by
    intro p hp
    have hpS := (Finset.mem_sdiff.mp hp).1
    have hpR := (Finset.mem_sdiff.mp hp).2
    have hpo : value C (fun q => decide (q = p)) o = true := (mem_support C o p).mp (hsupp.symm ▸ hpS)
    obtain ⟨w, hwB, hwp⟩ := hBcov p ⟨o, Finset.mem_singleton_self o, hpo⟩
    exact Finset.mem_biUnion.mpr ⟨w, hwB, Finset.mem_inter.mpr
      ⟨(mem_support C w p).mpr hwp, Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hpR⟩⟩⟩
  have h3 := Finset.card_filter_le G (· < n + C.size)
  simp only [Finset.card_singleton, Bool.false_eq_true, ↓reduceIte] at hBcard
  split_ifs with hne
  · obtain ⟨r, hr⟩ := hne
    have hrS := (Finset.mem_inter.mp hr).1
    have hrR := (Finset.mem_inter.mp hr).2
    cases hit' with
    | true =>
      simp only [↓reduceIte] at hBcard
      have h1 := Finset.card_le_card hcovU
      have h2 := Finset.card_biUnion_le_card_mul B (fun w => support C w ∩ U) 1 hsmallU
      change _ ≤ G.card
      omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hBcard
      have hsmallAll : ∀ w ∈ B, (support (n := n) C w).card ≤ 1 := by
        intro w hw
        have hsub := hBsub rfl w hw
        by_contra! hlarge
        have hwg := support_gate C w (by omega)
        have hwG : w ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hwg, Or.inr ⟨hsub, by omega⟩⟩
        exact Finset.disjoint_left.mp hdisj hw hwG
      have hcovAll : insert r (S \ R) ⊆ B.biUnion (support C) := by
        intro p hp
        have hpS : p ∈ S := by
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact hrS
          · exact (Finset.mem_sdiff.mp hp').1
        have hpo : value C (fun q => decide (q = p)) o = true := (mem_support C o p).mp (hsupp.symm ▸ hpS)
        obtain ⟨w, hwB, hwp⟩ := hBcov p ⟨o, Finset.mem_singleton_self o, hpo⟩
        exact Finset.mem_biUnion.mpr ⟨w, hwB, (mem_support C w p).mpr hwp⟩
      have h1 := Finset.card_le_card hcovAll
      have h2 := Finset.card_biUnion_le_card_mul B (support C) 1 hsmallAll
      have hrnot : r ∉ S \ R := fun h => (Finset.mem_sdiff.mp h).2 hrR
      rw [Finset.card_insert_of_notMem hrnot] at h1
      change _ ≤ G.card
      omega
  · have h1 := Finset.card_le_card hcovU
    have h2 := Finset.card_biUnion_le_card_mul B (fun w => support C w ∩ U) 1 hsmallU
    change _ ≤ G.card
    cases hit' <;> simp only [↓reduceIte, Bool.false_eq_true] at hBcard <;> omega

lemma owned_disjoint {n : ℕ} (C : Circuit) (U S₁ S₂ : Finset (Fin n))
    (hint : (S₁ ∩ S₂).card ≤ 1) :
    Disjoint (owned C U S₁) (owned C U S₂) := by
  refine Finset.disjoint_left.mpr fun w h1 h2 => ?_
  have c1 := (Finset.mem_filter.mp h1).2
  have c2 := (Finset.mem_filter.mp h2).2
  rcases c1 with ⟨hs1, hc1⟩ | ⟨hs1, hc1⟩ <;> rcases c2 with ⟨hs2, hc2⟩ | ⟨hs2, hc2⟩
  · have hsub : support C w ∩ U ⊆ S₁ ∩ S₂ := Finset.subset_inter hs1 hs2
    have := Finset.card_le_card hsub
    omega
  · have hsub : support C w ∩ U ⊆ S₁ ∩ S₂ :=
      Finset.subset_inter hs1 (Finset.inter_subset_left.trans hs2)
    have := Finset.card_le_card hsub
    omega
  · have hsub : support C w ∩ U ⊆ S₁ ∩ S₂ :=
      Finset.subset_inter (Finset.inter_subset_left.trans hs1) hs2
    have := Finset.card_le_card hsub
    omega
  · have hsub : support C w ⊆ S₁ ∩ S₂ := Finset.subset_inter hs1 hs2
    have := Finset.card_le_card hsub
    omega

end PEqualNP.Outside.L_meta_1375

theorem PEqualNP.Outside.L_meta_1375 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      ((∀ v ∈ S i0, x v = false) ∨ (∃ p ∈ S i0, ∀ v : Fin n, x v = decide (v = p))) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    m * q ≤ gates.length := by
  intro q n m S i0 _ hScard hSint gates out hgate heval
  classical
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
  have hCsize : C.size = gates.length := rfl
  have hCgood : PEqualNP.Outside.L_meta_1375.good C := hgate
  have hC_single : ∀ (i : Fin m) (p : Fin n),
      PEqualNP.Outside.L_meta_1375.value C (fun v => decide (v = p)) (out i) = decide (p ∈ S i) := by
    intro i p
    have hcond : (∀ v ∈ S i0, decide (v = p) = false) ∨
        (∃ p' ∈ S i0, ∀ v : Fin n, decide (v = p) = decide (v = p')) := by
      by_cases hpR : p ∈ S i0
      · exact Or.inr ⟨p, hpR, fun _ => rfl⟩
      · exact Or.inl (fun v hv => by simp [show v ≠ p from fun e => hpR (e ▸ hv)])
    change PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out i⟩
      (List.ofFn (fun v => decide (v = p))) = decide (p ∈ S i)
    rw [heval i _ hcond]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨v, hvS, hvp⟩
      have : v = p := of_decide_eq_true hvp
      exact this ▸ hvS
    · intro hpS
      exact ⟨p, hpS, decide_eq_true rfl⟩
  have hC_supp : ∀ i : Fin m, PEqualNP.Outside.L_meta_1375.support C (out i) = S i := by
    intro i
    ext p
    rw [PEqualNP.Outside.L_meta_1375.mem_support, hC_single i p, decide_eq_true_iff]
  have hC_offR : ∀ (i : Fin m) (A : Finset (Fin n)), Disjoint A (S i0) → Disjoint A (S i) →
      PEqualNP.Outside.L_meta_1375.value C (PEqualNP.Outside.L_meta_1375.bit A) (out i) = false := by
    intro i A hAR hAS
    have hcond : (∀ v ∈ S i0, PEqualNP.Outside.L_meta_1375.bit A v = false) ∨
        (∃ p ∈ S i0, ∀ v : Fin n, PEqualNP.Outside.L_meta_1375.bit A v = decide (v = p)) := by
      refine Or.inl fun v hv => ?_
      simp [PEqualNP.Outside.L_meta_1375.bit, Finset.disjoint_right.mp hAR hv]
    change PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out i⟩
      (List.ofFn (PEqualNP.Outside.L_meta_1375.bit A)) = false
    rw [heval i _ hcond]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hvS
    simp [PEqualNP.Outside.L_meta_1375.bit, Finset.disjoint_right.mp hAS hvS]
  let U : Finset (Fin n) := Finset.univ \ S i0
  let G : Fin m → Finset ℕ := fun i => PEqualNP.Outside.L_meta_1375.owned C U (S i)
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G :=
    fun i _ i' _ hne => PEqualNP.Outside.L_meta_1375.owned_disjoint C U (S i) (S i') (hSint i i' hne)
  have hsumG : ∑ i : Fin m, (G i).card ≤ gates.length := by
    have hbi : (Finset.univ.biUnion G).card ≤ (Finset.Ico n (n + C.size)).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hwi).1
    rw [Finset.card_biUnion hdisj, Nat.card_Ico, hCsize] at hbi
    omega
  have hbound : ∀ i : Fin m, q ≤ (G i).card := by
    intro i
    by_cases hii0 : i = i0
    · subst hii0
      have hc := PEqualNP.Outside.L_meta_1375.count_eq_R C hCgood U (S i) (out i)
        (hC_supp i) (hC_offR i (Finset.univ \ S i)
          (Finset.disjoint_left.mpr fun v hv hvS => (Finset.mem_sdiff.mp hv).2 hvS)
          (Finset.disjoint_left.mpr fun v hv hvS => (Finset.mem_sdiff.mp hv).2 hvS))
      rw [hScard i] at hc
      change q + 1 - 1 ≤ (G i).card at hc
      omega
    · have hgi := PEqualNP.Outside.L_meta_1375.count_general C hCgood (S i0) (S i) (out i)
        (hC_supp i) (hC_offR i ((Finset.univ \ S i0) \ S i)
          (Finset.disjoint_left.mpr fun v hv hvR =>
            (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hvR)
          (Finset.disjoint_left.mpr fun v hv hvS => (Finset.mem_sdiff.mp hv).2 hvS))
      have hsp : (S i \ S i0).card + (S i ∩ S i0).card = q + 1 := by
        rw [Finset.card_sdiff_add_card_inter, hScard i]
      have hint := hSint i i0 hii0
      change _ ≤ (G i).card at hgi
      by_cases hne : (S i ∩ S i0).Nonempty
      · have hpos : 1 ≤ (S i ∩ S i0).card := Finset.Nonempty.card_pos hne
        simp only [hne, ↓reduceIte] at hgi
        omega
      · have hzero : (S i ∩ S i0).card = 0 := Finset.not_nonempty_iff_eq_empty.mp hne ▸ rfl
        simp only [hne, ↓reduceIte] at hgi
        omega
  have hsum : m * q ≤ ∑ i : Fin m, (G i).card := by
    calc m * q = ∑ _ : Fin m, q := by simp
      _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ => hbound i
  omega
