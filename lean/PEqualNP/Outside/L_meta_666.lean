import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_666
open PEqualNP.CircuitLowerBounds
private abbrev Points := Finset (Fin 7)
private def line (w : Fin 7) : Points := ({0, 1, 3} : Points).image (fun u => u + w)
-- On singleton inputs each wire is a set of points. When a line first appears
-- as a union, a two-point operand identifies that line. For an intersection,
-- a four-point operand identifies the line, or both operands have five points.
-- A five-point set contains at most two lines, so it can pay one unit to each.
private def credit (w : Fin 7) (s : Points) : ℕ :=
  if s = line w then 2
  else if s.card = 2 ∧ s ⊆ line w then 2
  else if line w ⊆ s ∧ s.card = 4 then 2
  else if line w ⊆ s ∧ s.card = 5 then 1 else 0

private lemma three : ∀ w, (line w).card = 3 := by decide
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
private lemma capacity : ∀ s : Points, (∑ w, credit w s) ≤ 2 := by decide +kernel

private lemma pairCredit (w : Fin 7) (a b : Points) (ha : a ≠ line w) (hb : b ≠ line w)
    (h : a ∪ b = line w ∨ a ∩ b = line w) : 2 ≤ credit w a + credit w b := by
  have hc := three w
  have count := Finset.card_union_add_card_inter a b
  rcases h with u | m
  · have sa : a ⊆ line w := u ▸ Finset.subset_union_left
    have sb : b ⊆ line w := u ▸ Finset.subset_union_right
    have la := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sa,ha⟩)
    have lb := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sb,hb⟩)
    rw [u] at count
    have alt : a.card = 2 ∨ b.card = 2 := by omega
    rcases alt with aa|bb
    · simp [credit,ha,aa,sa]
    · simp [credit,hb,bb,sb]
  · have sa : line w ⊆ a := m ▸ Finset.inter_subset_left
    have sb : line w ⊆ b := m ▸ Finset.inter_subset_right
    have la := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sa,Ne.symm ha⟩)
    have lb := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sb,Ne.symm hb⟩)
    have upper : (a ∪ b).card ≤ 7 := by simpa using Finset.card_le_univ (a ∪ b)
    rw [m] at count
    by_cases aa : a.card = 4
    · simp [credit,ha,aa,sa]
    by_cases bb : b.card = 4
    · simp [credit,hb,bb,sb]
    have aa' : a.card = 5 := by omega
    have bb' : b.card = 5 := by omega
    simp [credit,ha,hb,sa,sb,aa',bb']

private def points (s : List Points) : Finset Points := insert ∅ s.toFinset
-- A completed line has two units from its own wire and two from its operands.
private def Good (S : Finset Points) := ∀ w, line w ∈ S → 4 ≤ ∑ b ∈ S, credit w b
private def charge (S : Finset Points) := ∑ w, ∑ b ∈ S, credit w b

private lemma addCost (S : Finset Points) (a : Points) :
    charge (insert a S) ≤ charge S + 2 := by
  by_cases h : a ∈ S
  · simp [h]
  simp only [charge,Finset.sum_insert h,Finset.sum_add_distrib]
  have := capacity a
  omega

private lemma extend (S : Finset Points) (z : Points) (good : Good S)
    (orig : ∀ w, z = line w → z ∉ S →
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ (a ∪ b = z ∨ a ∩ b = z)) : Good (insert z S) := by
  intro w hw
  by_cases hz : z ∈ S
  · simpa [hz] using good w (by simpa [hz] using hw)
  rw [Finset.sum_insert hz]
  rcases Finset.mem_insert.mp hw with h | h
  · subst z
    obtain ⟨a,ha,b,hb,ne,rel⟩ := orig w rfl hz
    have h1 := pairCredit w a b (fun e => hz (e ▸ ha)) (fun e => hz (e ▸ hb)) rel
    have sub : ({a,b} : Finset Points) ⊆ S := by
      intro y hy
      simp only [Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with rfl|rfl <;> assumption
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg sub (f := credit w) (by intros; omega)
    simp [ne] at h2
    have h3 : credit w (line w) = 2 := by simp [credit]
    omega
  · have := good w h
    omega

private def bit (v : Fin 7) (s : Points) : Bool := decide (v ∈ s)
private def result (op : GateOp) (args : List Points) : Points :=
  Finset.univ.filter fun v => op.eval (args.map (bit v))

private lemma isOrigin (S : Finset Points) (op : GateOp) (args : List Points)
    (hop : op = GateOp.and ∨ op = GateOp.or) (len : args.length ≤ 2)
    (hargs : ∀ x ∈ args, x ∈ S) (w : Fin 7)
    (eq : result op args = line w) (fresh : result op args ∉ S) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ (a ∪ b = result op args ∨ a ∩ b = result op args) := by
  cases args with
  | nil =>
    have c := three w
    rw [← eq] at c
    rcases hop with rfl|rfl <;> simp [result,GateOp.eval] at c
  | cons a rest =>
    have ha := hargs a (by simp)
    cases rest with
    | nil =>
      have e : result op [a] = a := by
        ext v
        rcases hop with rfl|rfl <;> simp [result,bit,GateOp.eval]
      exact (fresh (by rwa [e])).elim
    | cons b tail =>
      cases tail with
      | cons c rest => simp at len
      | nil =>
        have hb := hargs b (by simp)
        have alt : a ∪ b = result op [a,b] ∨ a ∩ b = result op [a,b] := by
          rcases hop with rfl|rfl
          · right; ext v; simp [result,bit,GateOp.eval]
          · left; ext v; simp [result,bit,GateOp.eval]
        refine ⟨a,ha,b,hb,?_,alt⟩
        rintro rfl
        rcases alt with e|e <;> simp at e <;> exact fresh (e ▸ ha)

private lemma readMem (s : List Points) (i : ℕ) : s.getD i ∅ ∈ points s := by
  rw [List.getD_eq_getElem?_getD]
  cases e : s[i]? with
  | none => simp [points]
  | some b => simpa [points] using Or.inr (a := b = ∅) (List.mem_of_getElem? e)

private def value (s : List Points) (g : Gate) := result g.op (g.inputs.map fun i => s.getD i ∅)
private def step (s : List Points) (g : Gate) := s ++ [value s g]
private def legal (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

private lemma ledger (gs : List Gate) (s : List Points) (hg : ∀ g ∈ gs, legal g)
    (ok : Good (points s)) :
    Good (points (gs.foldl step s)) ∧ charge (points (gs.foldl step s)) ≤ charge (points s) + 2 * gs.length := by
  induction gs generalizing s with
  | nil => simpa using ok
  | cons g tail ih =>
    have h := hg g (by simp)
    have ps : points (step s g) = insert (value s g) (points s) := by
      ext v; simp [points,step]; tauto
    have next : Good (points (step s g)) := by
      rw [ps]
      apply extend _ _ ok
      apply isOrigin _ _ _ h.1 (by simpa using h.2)
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      exact readMem s i
    obtain ⟨a,b⟩ := ih (step s g) (fun x hx => hg x (by simp [hx])) next
    refine ⟨a,?_⟩
    have d := addCost (points s) (value s g)
    rw [← ps] at d
    simp only [List.foldl_cons,List.length_cons]
    omega

private def init : List Points := List.ofFn fun i : Fin 7 => ({i} : Points)
private lemma initialGood : Good (points init) := by unfold Good; decide +kernel
private lemma initialCost : charge (points init) = 0 := by decide +kernel

private lemma readBit (s : List Points) (v : Fin 7) (i : ℕ) :
    (s.map (bit v)).getD i false = bit v (s.getD i ∅) := by
  exact List.getD_map s ∅ (bit v)

private lemma simulate (gs : List Gate) (s : List Points) (v : Fin 7) :
    (gs.foldl step s).map (bit v) = gs.foldl
      (fun wires g => wires ++ [g.op.eval (g.inputs.map fun i => wires.getD i false)]) (s.map (bit v)) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g tail ih =>
    simp only [List.foldl_cons,ih]
    congr 1
    simp only [step,List.map_append,List.map_cons,List.map_nil,readBit]
    congr 2
    simp [value,result,bit,List.map_map,Function.comp_def]

private lemma lower (gs : List Gate) (out : Fin 7 → ℕ) (hg : ∀ g ∈ gs, legal g)
    (ev : ∀ w (x : Fin 7 → Bool), (∀ i j, x i = true → x j = true → i = j) →
      (Circuit.mk gs (out w)).eval (List.ofFn x) = decide (∃ v ∈ line w, x v = true)) :
    14 ≤ gs.length := by
  let s := gs.foldl step init
  have allLines (w : Fin 7) : line w ∈ points s := by
    have eq : s.getD (out w) ∅ = line w := by
      ext v
      let x : Fin 7 → Bool := fun i => decide (v = i)
      have light : ∀ i j, x i = true → x j = true → i = j := by simp [x]
      have h := ev w x light
      have start : init.map (bit v) = List.ofFn x := by simp [init,bit,x]
      have sim := simulate gs init v
      rw [start] at sim
      simp only [Circuit.eval,Circuit.wires,←sim,readBit] at h
      simpa [s,bit,x] using h
    rw [←eq]
    exact readMem s (out w)
  have ⟨good,bound⟩ := ledger gs init hg initialGood
  have each : ∀ w : Fin 7, 4 ≤ ∑ b ∈ points s, credit w b := fun w => good w (allLines w)
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 7))) (fun w _ => each w)
  change _ ≤ charge (points s) at total
  simp at total
  rw [initialCost] at bound
  change charge (points s) ≤ _ at bound
  omega

end PEqualNP.Outside.L_meta_666

theorem PEqualNP.Outside.L_meta_666 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j : Fin 7, x i = true → x j = true → i = j) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) → 14 ≤ gates.length := PEqualNP.Outside.L_meta_666.lower
