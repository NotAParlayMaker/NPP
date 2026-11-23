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

def value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

lemma eval_eq_value {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = value gs x o :=
  rfl

lemma input_value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    value gs x p = x p := by
  change (run gs (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : value gs x w = false := by
  change (run gs (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

lemma gate_value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gs.length) :
    let g := gs[w - n]'(by omega)
    value gs x w = g.op.eval (g.inputs.map fun r => if r < w then value gs x r else false) := by
  let j := w - n
  have hj : j < gs.length := by omega
  let g := gs[j]
  let earlier := run (gs.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run gs (List.ofFn x) = run (g :: gs.drop (j + 1)) earlier := by
    rw [run_split gs (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value gs x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run gs (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run gs (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value gs x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + gs.length) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value gs x r = true → value gs y r = true) →
        value gs x w = true → value gs y w = true := by
  classical
  let g := gs[w - n]'(by omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value gs x r else false) = true →
        (if r < w then value gs y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value gs z w = g.op.eval (g.inputs.map fun r => if r < w then value gs z r else false) :=
      gate_value gs z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact hr r hrm (hx _ (List.mem_map.mpr ⟨r, hrm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hbt⟩ := hx
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hrm, rfl⟩, hr r hrm hbt⟩

lemma value_mono {n : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value gs x w = true → value gs y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value gs x p = true → value gs y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + gs.length
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs gs hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value gs x w (by omega)]

lemma cut {n : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + gs.length)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value gs x w = true → value gs y w = true) →
        ∀ w ∈ F, value gs x w = true → value gs y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs gs hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
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
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def single {n : ℕ} (p : Fin n) : Fin n → Bool :=
  fun v => decide (v = p)

def coff {n : ℕ} (T Sw : Finset (Fin n)) : Fin n → Bool :=
  fun v => decide (v ∉ Sw ∧ v ∉ T)

def active {n : ℕ} (gs : List Gate) (u : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value gs (single p) u = true)

lemma mem_active {n : ℕ} (gs : List Gate) (u : ℕ) (p : Fin n) :
    p ∈ active gs u ↔ value gs (single p) u = true := by
  simp [active]

def offSound {n : ℕ} (gs : List Gate) (T Sw : Finset (Fin n)) (u : ℕ) : Prop :=
  value gs (coff T Sw) u = false

def Good {n : ℕ} (gs : List Gate) (T Sw : Finset (Fin n)) (u : ℕ) : Prop :=
  offSound gs T Sw u ∧ (2 ≤ (active (n := n) gs u \ T).card ∨ (active (n := n) gs u ⊆ Sw ∧ 2 ≤ (active (n := n) gs u).card))

noncomputable def assigned {n : ℕ} (gs : List Gate) (T Sw : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + gs.length)).filter (fun u => Good gs T Sw u)

lemma mem_assigned {n : ℕ} (gs : List Gate) (T Sw : Finset (Fin n)) (u : ℕ) :
    u ∈ assigned gs T Sw ↔ (n ≤ u ∧ u < n + gs.length) ∧ Good gs T Sw u := by
  classical
  unfold assigned
  rw [Finset.mem_filter, Finset.mem_Ico]

lemma offSound_sdiff_subset {n : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T Sw : Finset (Fin n)) (u : ℕ) (hs : offSound gs T Sw u) :
    active gs u \ T ⊆ Sw := by
  intro p hp
  rw [Finset.mem_sdiff, mem_active] at hp
  by_contra hpS
  have hle : ∀ v : Fin n, single p v = true → coff T Sw v = true := by
    intro v hv
    have hvp : v = p := by simpa [single] using hv
    subst hvp
    simp [coff, hpS, hp.2]
  have htrue := value_mono gs hG (single p) (coff T Sw) hle u hp.1
  rw [hs] at htrue
  exact Bool.false_ne_true htrue

lemma good_card_ge_two {n : ℕ} (gs : List Gate) (T Sw : Finset (Fin n)) (u : ℕ)
    (hg : Good gs T Sw u) : 2 ≤ (active (n := n) gs u).card := by
  rcases hg.2 with h1 | h2
  · exact le_trans h1 (Finset.card_le_card Finset.sdiff_subset)
  · exact h2.2

lemma good_in_range {n : ℕ} (gs : List Gate) (T Sw : Finset (Fin n)) (u : ℕ)
    (hg : Good gs T Sw u) : n ≤ u ∧ u < n + gs.length := by
  have h2 := good_card_ge_two gs T Sw u hg
  constructor
  · by_contra! hu
    let p0 : Fin n := ⟨u, hu⟩
    have hsub : active gs u ⊆ {p0} := by
      intro q hq
      have hv := (mem_active gs u q).mp hq
      change value gs (single q) p0 = true at hv
      rw [input_value] at hv
      have : p0 = q := by simpa [single] using hv
      simp [this]
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_contra! hu
    have hempty : active (n := n) gs u = ∅ := by
      ext q
      simp [mem_active, missing_value gs _ u hu]
    simp [hempty] at h2

lemma good_unique {n m : ℕ} (S : Fin m → Finset (Fin n)) (i0 : Fin m)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w1 w2 : Fin m) (u : ℕ)
    (h1 : Good gs (S i0) (S w1) u) (h2 : Good gs (S i0) (S w2) u) : w1 = w2 := by
  by_contra hne
  have hint := hinter w1 w2 hne
  by_cases hdiff : 2 ≤ (active gs u \ S i0).card
  · have hsub : active gs u \ S i0 ⊆ S w1 ∩ S w2 := by
      intro p hp
      exact Finset.mem_inter.mpr
        ⟨offSound_sdiff_subset gs hG (S i0) (S w1) u h1.1 hp,
         offSound_sdiff_subset gs hG (S i0) (S w2) u h2.1 hp⟩
    have := Finset.card_le_card hsub
    omega
  · have h1r : active (n := n) gs u ⊆ S w1 ∧ 2 ≤ (active (n := n) gs u).card := h1.2.resolve_left hdiff
    have h2r : active (n := n) gs u ⊆ S w2 ∧ 2 ≤ (active (n := n) gs u).card := h2.2.resolve_left hdiff
    have hsub : active (n := n) gs u ⊆ S w1 ∩ S w2 := Finset.subset_inter h1r.1 h2r.1
    have := Finset.card_le_card hsub
    omega

lemma card_assigned_ge {q n m : ℕ} (S : Fin m → Finset (Fin n)) (i0 : Fin m)
    (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsingle : ∀ (w : Fin m) (p : Fin n), value gs (single p) (out w) = decide (p ∈ S w))
    (hcoff : ∀ (w : Fin m), value gs (coff (S i0) (S w)) (out w) = false)
    (w : Fin m) :
    q ≤ (assigned gs (S i0) (S w)).card := by
  classical
  let T := S i0
  let G := assigned gs T (S w)
  by_contra! hsmall
  have hGates : ∀ u ∈ G, n ≤ u ∧ u < n + gs.length :=
    fun u hu => ((mem_assigned gs T (S w) u).mp hu).1
  obtain ⟨B, hdisj, hBcard, hcut⟩ := cut gs hG G hGates (n + gs.length) {out w}
    (fun u _ hu => (hGates u hu).2)
  have hBle : B.card ≤ q := by
    have hGsmall : G.card < q := hsmall
    have hfl := Finset.card_filter_le G (fun u => u < n + gs.length)
    simp only [Finset.card_singleton] at hBcard
    omega
  have hnotGood : ∀ u ∈ B, ¬ Good gs T (S w) u := by
    intro u hu hgu
    exact Finset.disjoint_left.mp hdisj hu
      ((mem_assigned gs T (S w) u).mpr ⟨good_in_range gs T (S w) u hgu, hgu⟩)
  let Bs := B.filter (fun u => offSound gs T (S w) u)
  have contra_coff (p : Fin n) (hpS : p ∈ S w) (hpnot : ∀ u ∈ Bs, p ∉ active gs u) : False := by
    have ht : value gs (coff T (S w)) (out w) = true := by
      apply hcut (single p) (coff T (S w)) _ (out w) (Finset.mem_singleton_self _)
      · rw [hsingle w p]
        exact decide_eq_true hpS
      · intro u hu hup
        by_cases hs : offSound gs T (S w) u
        · exact False.elim (hpnot u (Finset.mem_filter.mpr ⟨hu, hs⟩) ((mem_active gs u p).mpr hup))
        · unfold offSound at hs
          cases hv : value gs (coff T (S w)) u
          · exact False.elim (hs hv)
          · rfl
    rw [hcoff w] at ht
    exact Bool.false_ne_true ht
  by_cases hwi : w = i0
  · subst hwi
    have hle1 : ∀ u ∈ Bs, (active (n := n) gs u).card ≤ 1 := by
      intro u hu
      have huB := (Finset.mem_filter.mp hu).1
      have hus := (Finset.mem_filter.mp hu).2
      have hsub : active gs u ⊆ T := by
        intro p hp
        by_contra hpT
        exact hpT (offSound_sdiff_subset gs hG T T u hus (Finset.mem_sdiff.mpr ⟨hp, hpT⟩))
      by_contra! hgt
      exact hnotGood u huB ⟨hus, Or.inr ⟨hsub, by omega⟩⟩
    have hcov : (Bs.biUnion (active (n := n) gs)).card < (S w).card := by
      have h1 := Finset.card_biUnion_le_card_mul Bs (active (n := n) gs) 1 hle1
      have h2 : Bs.card ≤ B.card := Finset.card_le_card (Finset.filter_subset _ B)
      have h3 := hcard w
      simp only [mul_one] at h1
      omega
    obtain ⟨p, hpS, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcov
    exact contra_coff p hpS (fun u hu hpa => hpnot (Finset.mem_biUnion.mpr ⟨u, hu, hpa⟩))
  · have hle1 : ∀ u ∈ Bs, (active gs u \ T).card ≤ 1 := by
      intro u hu
      have huB := (Finset.mem_filter.mp hu).1
      have hus := (Finset.mem_filter.mp hu).2
      by_contra! hgt
      exact hnotGood u huB ⟨hus, Or.inl (by omega)⟩
    by_cases hmiss : ∃ p ∈ S w \ T, p ∉ Bs.biUnion (fun u => active gs u \ T)
    · obtain ⟨p, hp, hpnot⟩ := hmiss
      rw [Finset.mem_sdiff] at hp
      exact contra_coff p hp.1 fun u hu hpa =>
        hpnot (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_sdiff.mpr ⟨hpa, hp.2⟩⟩)
    · push Not at hmiss
      have hsubU : S w \ T ⊆ Bs.biUnion (fun u => active gs u \ T) := hmiss
      have hinter1 : (S w ∩ T).card ≤ 1 := hinter w i0 hwi
      have hdiff_ge : q ≤ (S w \ T).card := by
        have hadd := Finset.card_sdiff_add_card_inter (S w) T
        have hc := hcard w
        omega
      have hUle : (Bs.biUnion (fun u => active gs u \ T)).card ≤ Bs.card := by
        have h1 := Finset.card_biUnion_le_card_mul Bs (fun u => active gs u \ T) 1 hle1
        simpa only [mul_one] using h1
      have hBsle : Bs.card ≤ B.card :=
        Finset.card_le_card (Finset.filter_subset _ B)
      have hSdiff_le : (S w \ T).card ≤ (Bs.biUnion (fun u => active gs u \ T)).card :=
        Finset.card_le_card hsubU
      have hBseq : Bs.card = B.card := by omega
      have hBs_eq_B : Bs = B := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ B) (by omega)
      have hBcard_eq : B.card = q := by omega
      have hUcard_eq : (Bs.biUnion (fun u => active gs u \ T)).card = q := by omega
      have hcard_inter_eq : (S w ∩ T).card = 1 := by
        have hadd := Finset.card_sdiff_add_card_inter (S w) T
        have hc := hcard w
        omega
      obtain ⟨pw, hpw⟩ := Finset.card_eq_one.mp hcard_inter_eq
      have hpw_mem : pw ∈ S w ∩ T := by rw [hpw]; exact Finset.mem_singleton_self pw
      have hpwS : pw ∈ S w := (Finset.mem_inter.mp hpw_mem).1
      have hpwT : pw ∈ T := (Finset.mem_inter.mp hpw_mem).2
      have hcard_one : ∀ u ∈ Bs, (active gs u \ T).card = 1 := by
        intro u hu
        have hle := hle1 u hu
        by_contra hne1
        have hzero : (active gs u \ T).card = 0 := by omega
        have hempty : active gs u \ T = ∅ := Finset.card_eq_zero.mp hzero
        have heqU : Bs.biUnion (fun v => active gs v \ T) =
            (Bs.erase u).biUnion (fun v => active gs v \ T) := by
          ext x
          simp only [Finset.mem_biUnion, Finset.mem_erase]
          constructor
          · rintro ⟨v, hv, hxv⟩
            have hvu : v ≠ u := fun e => by subst e; simp [hempty] at hxv
            exact ⟨v, ⟨hvu, hv⟩, hxv⟩
          · rintro ⟨v, ⟨_, hv⟩, hxv⟩
            exact ⟨v, hv, hxv⟩
        have hsm := Finset.card_biUnion_le_card_mul (Bs.erase u) (fun v => active gs v \ T) 1
          (fun v hv => hle1 v (Finset.mem_of_mem_erase hv))
        rw [← heqU, Finset.card_erase_of_mem hu, mul_one] at hsm
        omega
      have huniq : ∀ u1 ∈ Bs, ∀ u2 ∈ Bs, ∀ a : Fin n,
          a ∈ active gs u1 \ T → a ∈ active gs u2 \ T → u1 = u2 := by
        intro u1 hu1 u2 hu2 a ha1 ha2
        by_contra hne
        have heq2 : active gs u2 \ T = {a} := by
          obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (hcard_one u2 hu2)
          rw [hb] at ha2 ⊢
          have hab : a = b := Finset.mem_singleton.mp ha2
          rw [hab]
        have heqU : Bs.biUnion (fun v => active gs v \ T) =
            (Bs.erase u2).biUnion (fun v => active gs v \ T) := by
          ext x
          simp only [Finset.mem_biUnion, Finset.mem_erase]
          constructor
          · rintro ⟨v, hv, hxv⟩
            by_cases hvu2 : v = u2
            · subst hvu2
              rw [heq2, Finset.mem_singleton] at hxv
              subst hxv
              exact ⟨u1, ⟨hne, hu1⟩, ha1⟩
            · exact ⟨v, ⟨hvu2, hv⟩, hxv⟩
          · rintro ⟨v, ⟨_, hv⟩, hxv⟩
            exact ⟨v, hv, hxv⟩
        have hsm := Finset.card_biUnion_le_card_mul (Bs.erase u2) (fun v => active gs v \ T) 1
          (fun v hv => hle1 v (Finset.mem_of_mem_erase hv))
        rw [← heqU, Finset.card_erase_of_mem hu2, mul_one] at hsm
        omega
      have hex_u0 : ∃ u0 ∈ Bs, pw ∈ active gs u0 := by
        by_contra! hno
        exact contra_coff pw hpwS hno
      obtain ⟨u0, hu0Bs, hpw0⟩ := hex_u0
      have hu0B : u0 ∈ B := (Finset.mem_filter.mp hu0Bs).1
      have hu0s : offSound gs T (S w) u0 := (Finset.mem_filter.mp hu0Bs).2
      obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp (hcard_one u0 hu0Bs)
      have ha_mem : a ∈ active gs u0 \ T := by rw [ha_eq]; exact Finset.mem_singleton_self a
      have ha_act : a ∈ active gs u0 := (Finset.mem_sdiff.mp ha_mem).1
      have ha_notT : a ∉ T := (Finset.mem_sdiff.mp ha_mem).2
      have haS : a ∈ S w := offSound_sdiff_subset gs hG T (S w) u0 hu0s ha_mem
      have hapw : a ≠ pw := fun e => ha_notT (e ▸ hpwT)
      have hcard2 : 2 ≤ (active (n := n) gs u0).card := by
        have hsub : ({a, pw} : Finset (Fin n)) ⊆ active gs u0 := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact ha_act
          · rw [Finset.mem_singleton.mp hx]; exact hpw0
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hapw] at this
      have hnotSub : ¬ active gs u0 ⊆ S w := fun hsub =>
        hnotGood u0 hu0B ⟨hu0s, Or.inr ⟨hsub, hcard2⟩⟩
      rw [Finset.not_subset] at hnotSub
      obtain ⟨r0, hr0_act, hr0_notS⟩ := hnotSub
      have hcut_ar : value gs (single r0) (out w) = true := by
        apply hcut (single a) (single r0) _ (out w) (Finset.mem_singleton_self _)
        · rw [hsingle w a]
          exact decide_eq_true haS
        · intro u hu hua
          have huBs : u ∈ Bs := by rwa [hBs_eq_B]
          have ha_u : a ∈ active gs u \ T := Finset.mem_sdiff.mpr ⟨(mem_active gs u a).mpr hua, ha_notT⟩
          have hu_eq : u = u0 := huniq u huBs u0 hu0Bs a ha_u ha_mem
          rw [hu_eq]
          exact (mem_active gs u0 r0).mp hr0_act
      rw [hsingle w r0] at hcut_ar
      exact hr0_notS (of_decide_eq_true hcut_ar)

end PEqualNP.Outside.L_meta_1375

open PEqualNP.Outside.L_meta_1375 in
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
  classical
  intro q n m S i0 _ hcard hinter gates out hG heval
  have hsingle : ∀ (w : Fin m) (p : Fin n), value gates (single p) (out w) = decide (p ∈ S w) := by
    intro w p
    have hok : (∀ v ∈ S i0, single p v = false) ∨ (∃ p' ∈ S i0, ∀ v : Fin n, single p v = decide (v = p')) := by
      by_cases hp : p ∈ S i0
      · exact Or.inr ⟨p, hp, fun _ => rfl⟩
      · exact Or.inl fun v hv => by
          have hvp : v ≠ p := fun e => hp (e ▸ hv)
          simp [single, hvp]
    have h1 := heval w (single p) hok
    rw [eval_eq_value] at h1
    rw [h1]
    simp [single]
  have hcoff : ∀ (w : Fin m), value gates (coff (S i0) (S w)) (out w) = false := by
    intro w
    have hok : (∀ v ∈ S i0, coff (S i0) (S w) v = false) ∨
        (∃ p' ∈ S i0, ∀ v : Fin n, coff (S i0) (S w) v = decide (v = p')) :=
      Or.inl fun v hv => by simp [coff, hv]
    have h1 := heval w (coff (S i0) (S w)) hok
    rw [eval_eq_value] at h1
    rw [h1]
    exact decide_eq_false (by rintro ⟨v, hv, hcv⟩; simp [coff, hv] at hcv)
  have hper : ∀ w : Fin m, q ≤ (assigned gates (S i0) (S w)).card :=
    fun w => card_assigned_ge S i0 hcard hinter gates out hG hsingle hcoff w
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m)))
      (fun w : Fin m => assigned gates (S i0) (S w)) := by
    intro w1 _ w2 _ hne
    change Disjoint (assigned gates (S i0) (S w1)) (assigned gates (S i0) (S w2))
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    exact hne (good_unique S i0 hinter gates hG w1 w2 u
      ((mem_assigned gates (S i0) (S w1) u).mp hu1).2
      ((mem_assigned gates (S i0) (S w2) u).mp hu2).2)
  have hsub : (Finset.univ : Finset (Fin m)).biUnion (fun w => assigned gates (S i0) (S w))
      ⊆ Finset.Ico n (n + gates.length) := by
    intro u hu
    obtain ⟨w, _, huw⟩ := Finset.mem_biUnion.mp hu
    exact Finset.mem_Ico.mpr ((mem_assigned gates (S i0) (S w) u).mp huw).1
  calc m * q = ∑ _w : Fin m, q := by simp
    _ ≤ ∑ w : Fin m, (assigned gates (S i0) (S w)).card := Finset.sum_le_sum fun w _ => hper w
    _ = ((Finset.univ : Finset (Fin m)).biUnion (fun w => assigned gates (S i0) (S w))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card := Finset.card_le_card hsub
    _ = gates.length := by simp
