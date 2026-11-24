import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3166

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom, List.foldl_cons, ← wiresFrom, ih]
    simp [step]
    omega

theorem getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom, List.foldl_cons, ← wiresFrom, ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_eq (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp

theorem getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def ren (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def down (i : ℕ) := if i < 9 then i else i - 1

def redir (t k i : ℕ) := if i = t then k else if i < t then down i else i - 2

theorem simulation (gs : List Gate) (f : ℕ → ℕ) (u v : List Bool)
    (hn : ∀ g ∈ gs, 9 ∉ g.inputs)
    (h : ∀ i, i ≠ 9 → v.getD (f i) false = u.getD i false)
    (hf : ∀ i j, i ≠ 9 → (f i = v.length + j ↔ i = u.length + j)) :
    ∀ i, i ≠ 9 → (wiresFrom (gs.map (ren f)) v).getD (f i) false =
      (wiresFrom gs u).getD i false := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    have he : (ren f g).inputs.map (fun i => v.getD i false) =
        g.inputs.map (fun i => u.getD i false) := by
      simp only [ren, List.map_map]
      apply List.map_congr_left
      intro i hi
      exact h i (fun e => hn g List.mem_cons_self (e ▸ hi))
    apply ih (step u g) (step v (ren f g)) (fun a ha => hn a (List.mem_cons_of_mem _ ha))
    · intro i hi
      have hf' := hf i 0 hi
      simp only [Nat.add_zero] at hf'
      unfold step
      rw [he]
      change (v ++ [g.op.eval _]).getD (f i) false = _
      by_cases eq : i = u.length
      · rw [hf'.2 eq, eq, getD_snoc_eq, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ (fun e => eq (hf'.1 e)), getD_snoc_ne _ _ _ eq, h i hi]
    · intro i j hi
      simpa [step, Nat.add_assoc, Nat.add_comm 1 j] using hf i (j+1) hi

theorem main (C : Circuit) (k : ℕ) (g : Gate) (hk : k = 0 ∨ k = 2)
    (fan : FanInTwo C) (out : C.output ≠ 9)
    (fil : C.gates.filter (fun q => decide (9 ∈ q.inputs)) = [g])
    (op : g.op = .or) (ins : g.inputs = [9,k] ∨ g.inputs = [k,9]) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0 && x 2]) := by
  have mem : g ∈ C.gates := List.mem_of_mem_filter (by rw [fil]; simp)
  obtain ⟨a,b,splitG⟩ := List.append_of_mem mem
  have gin : 9 ∈ g.inputs := by rcases ins with e|e <;> simp [e]
  have fl := congrArg List.length fil
  rw [splitG] at fl
  simp [List.filter_append, gin] at fl
  have none (q : Gate) (hq : q ∈ a ∨ q ∈ b) : 9 ∉ q.inputs := by
    intro hi
    rcases hq with ha|hb
    · have hm : q ∈ a.filter (fun r => decide (9 ∈ r.inputs)) := List.mem_filter.mpr ⟨ha,by simp [hi]⟩
      have := List.length_pos_of_mem hm
      omega
    · have hm : q ∈ b.filter (fun r => decide (9 ∈ r.inputs)) := List.mem_filter.mpr ⟨hb,by simp [hi]⟩
      have := List.length_pos_of_mem hm
      omega
  let t := 10 + a.length
  let f := redir t k
  let D : Circuit := ⟨a.map (ren down) ++ b.map (ren f), f C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ a.map (ren down) ++ b.map (ren f) at hq
    rcases List.mem_append.mp hq with ha|hb
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
      simpa [ren] using fan r (by rw [splitG]; simp [hr])
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hb
      simpa [ren] using fan r (by rw [splitG]; simp [hr])
  · change (a.map (ren down) ++ b.map (ren f)).length + 1 = C.gates.length
    simp [splitG]; omega
  · intro x
    let w := List.ofFn x
    let u := w ++ [x 0 && x 2]
    let U := wiresFrom a u
    let V := wiresFrom (a.map (ren down)) w
    have wl : w.length = 9 := List.length_ofFn
    have ul : u.length = 10 := by simp [u,wl]
    have Ul : U.length = t := by simp [U,length_wiresFrom,ul,t]
    have Vl : V.length = 9 + a.length := by simp [V,length_wiresFrom,wl]
    have hpre : ∀ i, i ≠ 9 → V.getD (down i) false = U.getD i false := by
      apply simulation a down u w (fun r hr => none r (Or.inl hr))
      · intro i hi
        by_cases small : i < 9
        · simp only [down,small, ↓reduceIte,u]
          exact (List.getD_append _ _ _ _ (by omega)).symm
        · rw [List.getD_eq_default _ _ (by simp [down,small]; omega),
            List.getD_eq_default _ _ (by omega)]
      · intro i j hi
        simp only [ul,wl,down]
        split <;> omega
    have kl : k < 9 := by omega
    have kFin : U.getD k false = w.getD k false := by
      rw [getD_wiresFrom_lt _ _ _ (by omega)]
      exact List.getD_append _ _ _ _ (by omega)
    have nine : U.getD 9 false = (x 0 && x 2) := by
      rw [getD_wiresFrom_lt _ _ _ (by omega)]
      change (w ++ [_]).getD 9 false = _
      simpa only [wl] using getD_snoc_eq w (x 0 && x 2)
    have absb : g.op.eval (g.inputs.map fun i => U.getD i false) = w.getD k false := by
      rcases ins with hi|hi <;> rw [op,hi] <;>
        simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
          Bool.or_false,nine,kFin] <;>
        rcases hk with rfl|rfl <;> simp [w] <;> cases x 0 <;> cases x 2 <;> decide
    have kval : V.getD k false = w.getD k false := by
      simpa only [down,kl, ↓reduceIte] using (hpre k (by omega)).trans kFin
    have SU : (step U g).length = t + 1 := by simp [step,Ul]
    have hpost := simulation b f (step U g) V (fun r hr => none r (Or.inr hr)) (by
      intro i hi
      by_cases hit : i = t
      · subst i
        rw [show f t = k by simp [f,redir]]
        unfold step
        rw [← Ul,getD_snoc_eq,absb,kval]
      · by_cases low : i < t
        · simp only [f,redir,hit,low,↓reduceIte,step]
          rw [List.getD_append _ _ _ _ (by omega),hpre i hi]
        · rw [List.getD_eq_default _ _ (by rw [show f i = i - 2 by simp [f,redir,hit,low], Vl]; dsimp [t] at hit low; omega),
              List.getD_eq_default _ _ (by omega)]) (by
      intro i j hi
      simp only [f,redir,down,Vl,SU,t]
      split_ifs <;> omega)
    change (wiresFrom (a.map (ren down) ++ b.map (ren f)) w).getD (f C.output) false =
      (wiresFrom C.gates u).getD C.output false
    rw [splitG]
    simpa only [wiresFrom,List.foldl_append,List.foldl_cons,V,U] using hpost C.output out

end PEqualNP.Outside.L_meta_3166

theorem PEqualNP.Outside.L_meta_3166 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x2 = (0 : ℕ) ∨ x2 = (2 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → x1.output ≠ (9 : ℕ) → List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) x1.gates = [x3] → x3.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3.inputs = [(9 : ℕ), x2] ∨ x3.inputs = [x2, (9 : ℕ)] → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + (1 : ℕ) = x1.size ∧ ∀ (x12 : Fin (9 : ℕ) → Bool), x11.eval (List.ofFn x12) = x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) := by
  intro C k g hk fan _ out fil op ins
  exact PEqualNP.Outside.L_meta_3166.main C k g hk fan out fil op ins
