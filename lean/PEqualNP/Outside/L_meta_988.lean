import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_988
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

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
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

def sample {n} (y : Finset (Fin n)) (p v : Fin n) : Bool := decide (v ∈ y ∨ v = p)
def outside {n} (S : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∉ S)
def hits {n} (C : Circuit) (S y : Finset (Fin n)) (w : ℕ) :=
  S.filter fun p => value C (sample y p) w = true
def charged {n} (C : Circuit) (S y : Finset (Fin n)) :=
  (Finset.Ico n (n+C.size)).filter fun w =>
    value C (outside S) w = false ∧ 2 ≤ (hits C S y w).card

lemma gate_of_hits {n} (C : Circuit) (S y : Finset (Fin n)) (w : ℕ)
    (hv : value C (outside S) w = false) (hh : 2 ≤ (hits C S y w).card)
    (hd : Disjoint y S) : w ∈ Finset.Ico n (n+C.size) := by
  apply Finset.mem_Ico.mpr
  constructor
  · by_contra! h
    let q : Fin n := ⟨w,h⟩
    change value C (outside S) q = false at hv
    have hq : q ∈ S := by simpa [input_value,outside] using hv
    have hy : q ∉ y := fun h => Finset.disjoint_left.mp hd h hq
    have hs : hits C S y w ⊆ {q} := by
      intro p hp
      have he := (Finset.mem_filter.mp hp).2
      change value C (sample y p) q = true at he
      simpa [input_value,sample,hy,eq_comm] using he
    have := Finset.card_le_card hs
    simp at this
    omega
  · by_contra! hw
    have he : hits C S y w = ∅ := by simp [hits,missing_value C _ w hw]
    simp [he] at hh

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma countOne {n} (C : Circuit) (S y : Finset (Fin n)) (o : ℕ)
    (hg : good C) (hd : Disjoint y S) (hn : value C (outside S) o = false)
    (hp : ∀ p ∈ S, value C (sample y p) o = true) :
    S.card ≤ (charged C S y).card + 1 := by
  classical
  let G := charged C S y
  have hgates (w) (hw : w ∈ G) := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B,hdis,hcard,hcut⟩ := cut C hg G hgates (n+C.size) {o} (fun w _ hw => (hgates w hw).2)
  let F := B.filter fun w => value C (outside S) w = false
  have small (w) (hw : w ∈ F) : (hits C S y w).card ≤ 1 := by
    obtain ⟨hb,hv⟩ := Finset.mem_filter.mp hw
    by_contra! h
    have hh : 2 ≤ (hits C S y w).card := by omega
    exact Finset.disjoint_left.mp hdis hb (Finset.mem_filter.mpr ⟨gate_of_hits C S y w hv hh hd,hv,hh⟩)
  have cov : S ⊆ F.biUnion (hits C S y) := by
    intro p hps
    by_contra h
    have hf := hcut (sample y p) (outside S) (by
      intro w hw hv
      by_contra! he
      exact h (Finset.mem_biUnion.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,Bool.eq_false_iff.mpr he⟩,
        Finset.mem_filter.mpr ⟨hps,hv⟩⟩)) o (Finset.mem_singleton_self _) (hp p hps)
    rw [hn] at hf
    contradiction
  have h1 := Finset.card_le_card cov
  have h2 := Finset.card_biUnion_le_card_mul F (hits C S y) 1 small
  have h3 : F.card ≤ B.card := Finset.card_filter_le ..
  have h4 := Finset.card_filter_le G (fun w => w < n+C.size)
  simp only [Finset.card_singleton] at hcard
  change S.card ≤ G.card + 1
  omega

lemma cross {n} (C : Circuit) (S T y z : Finset (Fin n)) (w : ℕ) (hg : good C)
    (hl : (S ∩ T).card ≤ 1) (hs : w ∈ charged C S y) (ht : w ∈ charged C T z) :
    ¬ Disjoint y T := by
  intro hd
  have hsub : hits C S y w ⊆ S ∩ T := by
    intro p hp
    obtain ⟨hps,hv⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_inter.mpr ⟨hps,?_⟩
    by_contra hpt
    have hm := value_mono C hg (sample y p) (outside T) (by
      intro q hq
      apply decide_eq_true
      rcases (of_decide_eq_true hq : q ∈ y ∨ q = p) with hy | rfl
      · exact Finset.disjoint_left.mp hd hy
      · exact hpt) w hv
    rw [(Finset.mem_filter.mp ht).2.1] at hm
    contradiction
  have ha := Finset.card_le_card hsub
  have hb := (Finset.mem_filter.mp hs).2.2
  omega
end PEqualNP.Outside.L_meta_988

open PEqualNP.Outside.L_meta_988 in
theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  classical
  intro n m D S y C o hl hd hg hout hpos hbound
  let G := fun i => charged C (S i) (y i)
  let W := Finset.Ico n (n+C.size)
  have hone (i) : (S i).card ≤ (G i).card + 1 := by
    apply countOne C _ _ (o i) hg (hd i) _ (hpos i)
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨p,hp,hv⟩ := hout i _ ht
    simpa [outside,hp] using hv
  have hsub (i) : G i ⊆ W := Finset.filter_subset ..
  have hsum : ∑ i, (G i).card ≤ D * C.gates.length := by
    calc
      _ = ∑ i, ∑ w ∈ W, (if w ∈ G i then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        congr 1
        ext w
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨hsub i h,h⟩,And.right⟩
      _ = ∑ w ∈ W, ∑ i : Fin m, (if w ∈ G i then 1 else 0 : ℕ) := Finset.sum_comm
      _ ≤ ∑ _w ∈ W, D := by
        apply Finset.sum_le_sum
        intro w _
        simp only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        apply hbound
        intro i hi j hj hij
        exact cross C _ _ _ _ w hg (hl i j hij) (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
      _ = _ := by simp [W,PEqualNP.CircuitLowerBounds.Circuit.size,Nat.mul_comm]
  calc
    _ ≤ ∑ i, ((G i).card + 1) := Finset.sum_le_sum fun i _ => hone i
    _ = (∑ i, (G i).card) + m := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_right hsum m
