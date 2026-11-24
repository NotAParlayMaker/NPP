import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1469_aux

-- The wire semantics and cut lemmas follow L-meta-1353.

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

def Step {n : ℕ} (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ) : Prop :=
  ∀ w, n ≤ w → w < n + C.size → ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∈ R → P.card ≤ 1) ∧
    (∀ r ∈ P, r < w) ∧
    ∀ (x y : Fin n → Bool), X x → X y → (∀ r ∈ P, value C x r = true → value C y r = true) →
      value C x w = true → value C y w = true

lemma value_mono {n : ℕ} (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ)
    (hS : Step C X R)
    (x y : Fin n → Bool) (hx : X x) (hy : X y) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, _, hP, hstep⟩ := hS w (by omega) hw
      exact hstep x y hx hy fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma cut {n : ℕ} (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ)
    (hS : Step C X R)
    (G : Finset ℕ) (hGates : ∀ w ∈ G ∪ R, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G ∪ R → w < t) :
    ∃ B : Finset ℕ, Disjoint B (G ∪ R) ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, X x → X y → (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ _ _ h => h⟩
  | succ t ih =>
    have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ t ∈ G ∪ R
    · obtain ⟨P, hPcard, hPR, hP, hp⟩ := hS t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G ∪ R → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hu := Finset.card_union_le (F.erase t) P
      have he := Finset.card_erase_add_one hex.1
      change F'.card ≤ _ at hu
      refine ⟨B, hd, ?_, ?_⟩
      · by_cases htG : t ∈ G
        · have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hg, hlt⟩
              by_cases h : w = t
              · exact Or.inl h
              · exact Or.inr ⟨hg, by omega⟩
            · rintro (rfl | ⟨hg, hlt⟩)
              · exact ⟨htG, by omega⟩
              · exact ⟨hg, by omega⟩
          rw [hfilter, Finset.card_insert_of_notMem (by simp)]
          omega
        · have htR : t ∈ R := (Finset.mem_union.mp hex.2).resolve_left htG
          have := hPR htR
          omega
      · intro x y hx hy hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y hx hy fun r hr => hi x y hx hy hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hx hy hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G ∪ R → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      exact ⟨B, hd, by omega, hi⟩

def offSet {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∉ T)

lemma weight {n : ℕ} (T : Finset (Fin n)) :
    (Finset.univ.filter (fun p => offSet T p = true)).card = n - T.card := by
  have h : Finset.univ.filter (fun p => offSet T p = true) = Tᶜ := by
    ext p
    simp [offSet]
  rw [h, Finset.card_compl, Fintype.card_fin]


def HasPair {n : ℕ} (x : Fin n → Bool) : Prop :=
  2 ≤ (Finset.univ.filter (fun v => x v = true)).card

theorem not_source {n : ℕ} (C : Circuit) (j : Fin C.gates.length) (hn : 3 ≤ n)
    (hop : (C.gates.get j).op = GateOp.not)
    (hzero : ∀ x : Fin n → Bool, HasPair x → value C x (n+j.val) = false) :
    ∃ u, n ≤ u ∧ u < n+j.val ∧ ∀ x : Fin n → Bool, HasPair x → value C x u = true := by
  classical
  have heq (x : Fin n → Bool) (hx : HasPair x) :
      GateOp.not.eval (C.gates[j.val].inputs.map
        (fun u => if u < n+j.val then value C x u else false)) = false := by
    have he := gate_value C x (n+j.val) (by omega) (by
      change n+j.val < n+C.gates.length
      omega)
    simp only [Nat.add_sub_cancel_left] at he
    change C.gates[j.val].op = GateOp.not at hop
    rw [hop, hzero x hx] at he
    exact he.symm
  let top : Fin n → Bool := fun _ => true
  have ht : HasPair top := by simpa [HasPair, top] using (show 2 ≤ n by omega)
  cases hin : C.gates[j.val].inputs with
  | nil =>
      have h := heq top ht
      simp [hin, GateOp.eval] at h
  | cons u tail =>
      have hval (x : Fin n → Bool) (hx : HasPair x) :
          (if u < n+j.val then value C x u else false) = true := by
        simpa [hin, GateOp.eval] using heq x hx
      have hu : u < n+j.val := by
        by_contra h
        simpa [h] using hval top ht
      have hv (x : Fin n → Bool) (hx : HasPair x) : value C x u = true := by
        simpa [hu] using hval x hx
      refine ⟨u, ?_, hu, hv⟩
      by_contra! h
      let p : Fin n := ⟨u, h⟩
      have hp : HasPair (offSet {p}) := by
        unfold HasPair
        rw [weight]
        simp
        omega
      have hfalse := hv (offSet {p}) hp
      change value C (offSet {p}) p = true at hfalse
      simp [input_value, offSet] at hfalse


-- Use the seven anchors as vertices of a Paley tournament.
private def paley (a b : Fin 7) : Bool :=
  let d := (b.val + 7 - a.val) % 7
  d == 1 || d == 2 || d == 4

private theorem paley_asymm : ∀ a b : Fin 7, paley a b = true → paley b a ≠ true := by decide

private theorem paley_pair : ∀ a b : Fin 7, ∃ c : Fin 7,
    paley a c = true ∧ paley b c = true := by decide

private theorem paley_small (T : Finset (Fin 7)) (hT : T.card ≤ 2) :
    ∃ c : Fin 7, ∀ t ∈ T, paley t c = true := by
  rcases (show T.card = 0 ∨ T.card = 1 ∨ T.card = 2 by omega) with h | h | h
  · have he := Finset.card_eq_zero.mp h
    exact ⟨0, by simp [he]⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    obtain ⟨c, hc, _⟩ := paley_pair a a
    exact ⟨c, by simpa using hc⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h
    obtain ⟨c, h₁, h₂⟩ := paley_pair a b
    exact ⟨c, by simpa using And.intro h₁ h₂⟩

theorem choosePivots {n m : ℕ} (S : Fin m → Finset (Fin n)) (A : Finset (Fin n))
    (hA : A.card = 7) (hSA : ∀ i, ((S i) ∩ A).card ≤ 2) :
    ∃ p : Fin m → Fin n, (∀ i, p i ∈ A) ∧ (∀ i, p i ∉ S i) ∧
      (∀ i j, p i ∈ S j → p j ∉ S i) := by
  classical
  let e : A ≃ Fin 7 := Finset.equivFinOfCardEq hA
  let enc (v : Fin n) : Fin 7 := if hv : v ∈ A then e ⟨v, hv⟩ else 0
  have he (a : A) : enc a.val = e a := by simp [enc, a.property]
  have pick (i : Fin m) : ∃ c : Fin 7, ∀ t ∈ (S i ∩ A).image enc, paley t c = true :=
    paley_small _ (Finset.card_image_le.trans (hSA i))
  choose c hc using pick
  let pivot (i : Fin m) := e.symm (c i)
  have ep (i : Fin m) : enc (pivot i : Fin n) = c i := (he _).trans (e.apply_symm_apply _)
  have arrow (i j : Fin m) (h : (pivot i : Fin n) ∈ S j) : paley (c i) (c j) = true := by
    rw [← ep i]
    exact hc j _ (Finset.mem_image.mpr ⟨_, Finset.mem_inter.mpr ⟨h, (pivot i).property⟩, rfl⟩)
  refine ⟨fun i => (pivot i : Fin n), fun i => (pivot i).property, ?_, ?_⟩
  · intro i h
    exact paley_asymm _ _ (arrow i i h) (arrow i i h)
  · intro i j h h'
    exact paley_asymm _ _ (arrow i j h) (arrow j i h')


def PairInput {n : ℕ} (a b : Fin n) (p : Fin n) : Bool := decide (p = a ∨ p = b)

lemma pair_large {n : ℕ} {a b : Fin n} (hne : a ≠ b) : HasPair (PairInput a b) := by
  classical
  have h : (Finset.univ.filter (fun p => PairInput a b p = true)) = {a, b} := by
    ext p
    simp [PairInput]
  rw [HasPair, h, Finset.card_pair hne]

def supported {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (a : Fin n) (w : ℕ) : Finset (Fin n) :=
  T.filter fun p => value C (PairInput p a) w = true

-- Count gates that distinguish at least two row points from the row complement.
def owned {n : ℕ} (C : Circuit) (R : Finset ℕ) (T : Finset (Fin n)) (a : Fin n) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => w ∉ R ∧ value C (offSet T) w = false ∧
    2 ≤ (supported C T a w).card

lemma cross_pivot {n : ℕ} (C : Circuit) (R : Finset ℕ) (T U : Finset (Fin n))
    (a b : Fin n) (ha : a ∉ T) (hU : HasPair (offSet U)) (hTU : (T ∩ U).card ≤ 1)
    (hS : Step (n := n) C HasPair R) {w : ℕ} (hi : w ∈ owned C R T a) (hj : w ∈ owned C R U b) : a ∈ U := by
  classical
  have hp : ∃ p ∈ supported C T a w, p ∉ U := by
    by_contra! h
    have hsub : supported C T a w ⊆ T ∩ U := fun p hp =>
      Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, h p hp⟩
    have hcard := Finset.card_le_card hsub
    have hown := (Finset.mem_filter.mp hi).2.2.2
    omega
  obtain ⟨p,hp,hpU⟩ := hp
  have hpa : p ≠ a := fun he => ha (he ▸ (Finset.mem_filter.mp hp).1)
  by_contra haU
  have hxy : ∀ x, PairInput p a x = true → offSet U x = true := by
    intro x hx
    simp only [PairInput, decide_eq_true_eq] at hx
    rcases hx with rfl | rfl
    · simp [offSet, hpU]
    · simp [offSet, haU]
  have ht := value_mono C HasPair R hS (PairInput p a) (offSet U) (pair_large hpa) hU hxy w
    ((Finset.mem_filter.mp hp).2)
  rw [(Finset.mem_filter.mp hj).2.2.1] at ht
  exact Bool.noConfusion ht

lemma owned_count {n q : ℕ} (C : Circuit) (R : Finset ℕ) (T : Finset (Fin n))
    (a : Fin n) (o : ℕ) (ha : a ∉ T) (hcard : T.card = q + 1) (hy : HasPair (offSet T))
    (hR : ∀ w ∈ R, n ≤ w ∧ w < n + C.size) (hS : Step (n := n) C HasPair R)
    (hout : value C (offSet T) o = false)
    (hpair : ∀ p ∈ T, value C (PairInput p a) o = true) : q ≤ (owned C R T a).card := by
  classical
  by_contra! hsmall
  let G := owned C R T a
  have hgate : ∀ w ∈ G ∪ R, n ≤ w ∧ w < n + C.size := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
    · exact hR w hw
  obtain ⟨B, hdis, hB, hcut⟩ := cut C HasPair R hS G hgate (n+C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hBq : B.card ≤ q := by
    have hf := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hB
    change G.card < q at hsmall
    omega
  let L (w : ℕ) := if value C (offSet T) w = false then supported C T a w else ∅
  have hL : ∀ w ∈ B, (L w).card ≤ 1 := by
    intro w hw
    by_cases hf : value C (offSet T) w = false
    · dsimp only [L]
      rw [if_pos hf]
      by_cases hraw : w < n
      · let p : Fin n := ⟨w, hraw⟩
        have hp : p ∈ T := by
          change value C (offSet T) p = false at hf
          simpa [input_value, offSet] using hf
        apply Finset.card_le_one.mpr
        intro b hb c hc
        have hb' := (Finset.mem_filter.mp hb).2
        have hc' := (Finset.mem_filter.mp hc).2
        change value C (PairInput b a) p = true at hb'
        change value C (PairInput c a) p = true at hc'
        have hpa : p ≠ a := fun h => ha (h ▸ hp)
        have hb'' : p = b := by simpa [input_value, PairInput, hpa] using hb'
        have hc'' : p = c := by simpa [input_value, PairInput, hpa] using hc'
        exact hb''.symm.trans hc''
      · by_cases hbound : w < n + C.size
        · by_contra! hh
          have hg : w ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hbound⟩,
            fun hr => Finset.disjoint_left.mp hdis hw (Finset.mem_union_right _ hr), hf, by omega⟩
          exact Finset.disjoint_left.mp hdis hw (Finset.mem_union_left _ hg)
        · have hnull : supported C T a w = ∅ := by
            ext b
            simp [supported, missing_value C (PairInput b a) w (by omega)]
          simp [hnull]
    · simp [L, hf]
  have hcov : (B.biUnion L).card ≤ q :=
    (Finset.card_biUnion_le_card_mul B L 1 hL).trans (by simpa using hBq)
  have hex : ∃ p ∈ T, p ∉ B.biUnion L := by
    by_contra! nh
    have := Finset.card_le_card (show T ⊆ B.biUnion L from nh)
    omega
  obtain ⟨p,hp,hn⟩ := hex
  have hpa : p ≠ a := fun he => ha (he ▸ hp)
  have hImp : ∀ w ∈ B, value C (PairInput p a) w = true → value C (offSet T) w = true := by
    intro w hw hv
    by_cases hf : value C (offSet T) w = false
    · exact False.elim <| hn <| Finset.mem_biUnion.mpr ⟨w,hw,by simp [L, hf, supported, hp, hv]⟩
    · simpa using hf
  have ht := hcut (PairInput p a) (offSet T) (pair_large hpa) hy hImp o
    (Finset.mem_singleton_self o) (hpair p hp)
  rw [hout] at ht
  exact Bool.noConfusion ht

lemma main : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    2 ≤ q → 1 ≤ m → q + 3 ≤ n → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ v : Fin n, ∃ i : Fin m, v ∈ S i) →
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, 2 ≤ (Finset.univ.filter (fun v => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by

  classical
  intro q n m S A _ _ hn hsize hinter _ hA hSA gates out j hg hj huniq heval hfalse
  have hjlt : (j : ℕ) < gates.length := j.isLt
  let C : Circuit := ⟨gates, 0⟩
  let X : (Fin n → Bool) → Prop := HasPair
  let Rd := Finset.univ.filter (fun i : Fin gates.length =>
    j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)
  let R₀ : Finset ℕ := insert (n + (j : ℕ)) (Rd.image (fun i : Fin gates.length => n + (i : ℕ)))
  have hjv : ∀ x, X x → value C x (n + (j : ℕ)) = false := fun x hx => hfalse x hx
  obtain ⟨u, hun, huj, hSource⟩ := not_source C j (by omega) hj hjv
  have hnotR : n + (j : ℕ) ∉ Rd.image (fun i : Fin gates.length => n + (i : ℕ)) := by
    intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    have hji := (Finset.mem_filter.mp hi).2.1
    have : (j : ℕ) < (i : ℕ) := hji
    omega
  have hR₀card : R₀.card = Rd.card + 1 := by
    rw [Finset.card_insert_of_notMem hnotR, Finset.card_image_of_injective]
    intro a b hab
    exact Fin.ext (by simpa using hab)
  have hR₀ : ∀ w ∈ R₀, n ≤ w ∧ w < n + C.size := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · rw [h]
      exact ⟨by omega, by change n + (j : ℕ) < n + gates.length; omega⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨by omega, by change n + (i : ℕ) < n + gates.length; omega⟩

  have hS₀ : Step C X R₀ := by
    intro w hn hw
    have hk : w - n < gates.length := by change w < n + gates.length at hw; omega
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    simp only [Nat.add_sub_cancel_left] at hk
    by_cases hkj : k = (j : ℕ)
    · refine ⟨∅, by simp, by simp, by simp, fun x y hx hy _ h => ?_⟩
      rw [hkj, hjv x hx] at h
      exact Bool.noConfusion h
    · have hop : gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or := by
        rcases (hg gates[k] (List.getElem_mem _)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (congrArg Fin.val (huniq ⟨k, hk⟩ h)) hkj
      have hlen := (hg gates[k] (List.getElem_mem _)).2
      let P0 := gates[k].inputs.toFinset.filter (· < n + k)
      have hP0 : P0.card ≤ 2 :=
        (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
      by_cases hR' : n + k ∈ R₀
      · have hrd : (j : ℕ) < k ∧ n + (j : ℕ) ∈ gates[k].inputs := by
          rcases Finset.mem_insert.mp hR' with h | h
          · omega
          · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
            have hik : (i : ℕ) = k := by omega
            have hi2 := (Finset.mem_filter.mp hi).2
            have e : i = ⟨k, hk⟩ := Fin.ext hik
            rw [e] at hi2
            exact ⟨hi2.1, hi2.2⟩
        have hmem : n + (j : ℕ) ∈ P0 :=
          Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hrd.2, by omega⟩
        refine ⟨P0.erase (n + (j : ℕ)), (Finset.card_erase_le).trans hP0, fun _ => ?_,
          fun r hr => (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).2, ?_⟩
        · have := Finset.card_erase_add_one hmem
          omega
        · intro x y hx hy hxy
          refine gate_mono C k hk hop x y fun r hm hlt hv => ?_
          by_cases hrj : r = n + (j : ℕ)
          · rw [hrj, hjv x hx] at hv
            exact Bool.noConfusion hv
          · exact hxy r (Finset.mem_erase.mpr ⟨hrj,
              Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, hlt⟩⟩) hv
      · refine ⟨P0, hP0, fun h => absurd h hR', fun r hr => (Finset.mem_filter.mp hr).2, ?_⟩
        intro x y _ _ hxy
        exact gate_mono C k hk hop x y fun r hm hlt hv =>
          hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, hlt⟩) hv

  -- The source of the NOT gate is constant true on the test domain.
  let R := insert u R₀
  have hunot : u ∉ R₀ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
      have hji : (j : ℕ) < (i : ℕ) := (Finset.mem_filter.mp hi).2.1
      omega
  have hRcard : R.card = Rd.card + 2 := by
    rw [Finset.card_insert_of_notMem hunot, hR₀card]
  have hR : ∀ w ∈ R, n ≤ w ∧ w < n + C.size := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · subst w
      exact ⟨hun, by change u < n + gates.length; omega⟩
    · exact hR₀ w h
  have hS : Step (n := n) C HasPair R := by
    intro w hwn hwl
    by_cases hw : w = u
    · subst w
      exact ⟨∅, by simp, by simp, by simp, fun x y hx hy _ _ => hSource y hy⟩
    · obtain ⟨P, hP, hPR, hPrev, hProp⟩ := hS₀ w hwn hwl
      exact ⟨P, hP, fun h => hPR ((Finset.mem_insert.mp h).resolve_left hw), hPrev, hProp⟩
  obtain ⟨p, _, hp, hcross⟩ := choosePivots S A hA hSA
  have hOff (i : Fin m) : HasPair (offSet (S i)) := by
    rw [HasPair, weight, hsize]
    omega
  have hOut (i : Fin m) (x : Fin n → Bool) :
      value C x (out i) = decide (∃ v ∈ S i, x v = true) := heval i x
  let G (i : Fin m) := owned C R (S i) (p i)
  have hOwn (i : Fin m) : q ≤ (G i).card := by
    apply owned_count C R (S i) (p i) (out i) (hp i) (hsize i) (hOff i) hR hS
    · rw [hOut]
      simp [offSet]
    · intro v hv
      rw [hOut]
      exact decide_eq_true ⟨v, hv, by simp [PairInput]⟩
  have hDis : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ k _ hik
    refine Finset.disjoint_left.mpr fun w hw hw' => ?_
    have h₁ := cross_pivot C R (S i) (S k) (p i) (p k) (hp i) (hOff k) (hinter i k hik) hS hw hw'
    have h₂ := cross_pivot C R (S k) (S i) (p k) (p i) (hp k) (hOff i) (hinter k i hik.symm) hS hw' hw
    exact hcross i k h₁ h₂
  have hUnion : (Finset.univ.biUnion G) ∪ R ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    · exact Finset.mem_Ico.mpr (hR w hw)
  have hRDis : Disjoint (Finset.univ.biUnion G) R := by
    refine Finset.disjoint_left.mpr fun w hw hr => ?_
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hi).2.1 hr
  have hSum : m * q ≤ (Finset.univ.biUnion G).card := by
    calc
      m * q = ∑ _i : Fin m, q := by simp
      _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum (fun i _ => hOwn i)
      _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hDis).symm
  have hAll := Finset.card_le_card hUnion
  rw [Finset.card_union_of_disjoint hRDis, hRcard] at hAll
  have hTotal : (Finset.Ico n (n + C.size)).card = gates.length := by simp [C, Circuit.size]
  rw [hTotal] at hAll
  change m * q + Rd.card + 2 ≤ gates.length
  omega

end PEqualNP.Outside.L_meta_1469_aux

theorem PEqualNP.Outside.L_meta_1469 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    2 ≤ q → 1 ≤ m → q + 3 ≤ n → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ v : Fin n, ∃ i : Fin m, v ∈ S i) →
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, 2 ≤ (Finset.univ.filter (fun v => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1469_aux.main
