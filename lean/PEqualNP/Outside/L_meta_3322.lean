import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_3322

def ao (g : GateOp) := g = GateOp.and ∨ g = GateOp.or

def key (a b c d : ℕ) := (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

def seed (x : Fin 14 → Bool) (a b : Fin 14) (o : GateOp) :=
  List.ofFn x ++ [o.eval [x a, x b]]

def second (w : List Bool) (c d : Fin 15) (o : GateOp) :=
  w ++ [o.eval [w.getD c.val false, w.getD d.val false]]

def feasible (F : (Fin 14 → Bool) → Bool) (a b : Fin 14) (c d : Fin 15) : Prop :=
  a < b ∧ c < d ∧ ∃ o q : GateOp, ∃ D : Circuit, ao o ∧ ao q ∧ Monotone2 D ∧ D.size ≤ 24 ∧
    ∀ x, D.eval (second (seed x a b o) c d q) = F x

lemma commEval (o : GateOp) (ho : ao o) (a b : Bool) : o.eval [a,b] = o.eval [b,a] := by
  rcases ho with rfl | rfl <;> cases a <;> cases b <;> rfl

lemma sortedEval {n : ℕ} (v : Fin n → Bool) (a b : Fin n) (o : GateOp) (ho : ao o) :
    o.eval [v (min a b),v (max a b)] = o.eval [v a,v b] := by
  rcases le_total a b with h | h
  · simp [min_eq_left h,max_eq_right h]
  · simpa [min_eq_right h,max_eq_left h] using commEval o ho (v b) (v a)

lemma sortFeasible {F} {a b : Fin 14} {c d : Fin 15} {o q : GateOp} {D : Circuit}
    (hab : a ≠ b) (hcd : c ≠ d) (ho : ao o) (hq : ao q) (hm : Monotone2 D)
    (hs : D.size ≤ 24) (h : ∀ x, D.eval (second (seed x a b o) c d q) = F x) :
    feasible F (min a b) (max a b) (min c d) (max c d) := by
  refine ⟨by rcases lt_or_gt_of_ne hab with h|h <;> simp [h.le,h],
    by rcases lt_or_gt_of_ne hcd with h|h <;> simp [h.le,h], o,q,D,ho,hq,hm,hs,?_⟩
  intro x
  have he : seed x (min a b) (max a b) o = seed x a b o := by simp only [seed, sortedEval x a b o ho]
  rw [he]
  have he' := sortedEval (fun i : Fin 15 => (seed x a b o).getD i.val false) c d q hq
  simpa only [second, he'] using h x

lemma two {l : List ℕ} (h : l.length = 2) : ∃ a b, l = [a,b] := by
  match l with
  | [a,b] => exact ⟨a,b,rfl⟩
  | [] | [_] | _ :: _ :: _ :: _ => simp at h

lemma readInput (x : Fin 14 → Bool) (i : Fin 14) : (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
  exact List.getElem_ofFn ..

lemma initial {F} (C : Circuit) (hm : IsAO2 14 C) (hn : ∀ g ∈ C.gates, g.inputs.Nodup)
    (hlo : 2 ≤ C.size) (hhi : C.size ≤ 26) (hf : ∀ x, C.eval (List.ofFn x) = F x) :
    ∃ a b c d, feasible F a b c d := by
  obtain ⟨gs,out⟩ := C
  match gs with
  | [] | [_] => simp [Circuit.size] at hlo
  | g :: k :: tail =>
    have mg : g ∈ g :: k :: tail := by simp
    have mk : k ∈ g :: k :: tail := by simp
    obtain ⟨a,b,hab⟩ := two (hm.2.2 g mg)
    obtain ⟨c,d,hcd⟩ := two (hm.2.2 k mk)
    have h₁ : ∀ i ∈ g.inputs, i < 14 := by simpa [NestedCover.gateAt] using hm.2.1 0 (by simp)
    have h₂ : ∀ i ∈ k.inputs, i < 15 := by simpa [NestedCover.gateAt] using hm.2.1 1 (by simp)
    let A : Fin 14 := ⟨a,h₁ a (by simp [hab])⟩
    let B : Fin 14 := ⟨b,h₁ b (by simp [hab])⟩
    let U : Fin 15 := ⟨c,h₂ c (by simp [hcd])⟩
    let V : Fin 15 := ⟨d,h₂ d (by simp [hcd])⟩
    let D : Circuit := ⟨tail,out⟩
    have hmD : Monotone2 D := by
      intro j hj
      have hj' : j ∈ g :: k :: tail := by simp [D] at hj; simp [hj]
      exact ⟨hm.1 j hj', (hm.2.2 j hj').le⟩
    refine ⟨min A B,max A B,min U V,max U V,sortFeasible (o := g.op) (q := k.op) (D := D) ?_ ?_ (hm.1 g mg) (hm.1 k mk) hmD ?_ ?_⟩
    · have hne : a ≠ b := by simpa [hab] using hn g mg
      exact fun h => hne (congrArg Fin.val h)
    · have hne : c ≠ d := by simpa [hcd] using hn k mk
      exact fun h => hne (congrArg Fin.val h)
    · simp [Circuit.size] at hhi
      change tail.length ≤ 24
      omega
    · intro x
      simpa only [Circuit.eval,Circuit.wires,seed,second,D,List.foldl_cons,hab,hcd,List.map_cons,List.map_nil,show (List.ofFn x).getD a false = x A from readInput x A,show (List.ofFn x).getD b false = x B from readInput x B] using hf x


def renameGate (ρ : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map ρ }

def renameCircuit (ρ : ℕ → ℕ) (C : Circuit) : Circuit :=
  { gates := C.gates.map (renameGate ρ), output := ρ C.output }

def wireRel (ρ : ℕ → ℕ) (w v : List Bool) : Prop :=
  ∀ i, v.getD (ρ i) false = w.getD i false

lemma wireRel_append (ρ : ℕ → ℕ) (n : ℕ)
    (hfix : ∀ i, n ≤ i → ρ i = i) (hlt : ∀ i, i < n → ρ i < n)
    (w v : List Bool) (hlen : w.length = v.length) (hn : n ≤ w.length)
    (hrel : wireRel ρ w v) (b : Bool) : wireRel ρ (w ++ [b]) (v ++ [b]) := by
  intro i
  by_cases hi : i < w.length
  · have hri : ρ i < v.length := by
      by_cases hin : i < n
      · have := hlt i hin
        omega
      · rw [hfix i (by omega)]
        omega
    rw [List.getD_append _ _ _ _ hri, List.getD_append _ _ _ _ hi]
    exact hrel i
  · have hin : n ≤ i := by omega
    rw [hfix i hin]
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

lemma wires_rename (ρ : ℕ → ℕ) (n : ℕ)
    (hfix : ∀ i, n ≤ i → ρ i = i) (hlt : ∀ i, i < n → ρ i < n)
    (gs : List Gate) (w v : List Bool) (hlen : w.length = v.length)
    (hn : n ≤ w.length) (hrel : wireRel ρ w v) :
    wireRel ρ
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      ((gs.map (renameGate ρ)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v) := by
  induction gs generalizing w v with
  | nil => exact hrel
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    have hval : (renameGate ρ g).op.eval
        ((renameGate ρ g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [renameGate, List.map_map]
      congr 2
      exact funext hrel
    rw [hval]
    apply ih
    · simp [hlen]
    · simp only [List.length_append, List.length_singleton]
      omega
    · exact wireRel_append ρ n hfix hlt w v hlen hn hrel _

lemma eval_rename (ρ : ℕ → ℕ) (n : ℕ)
    (hfix : ∀ i, n ≤ i → ρ i = i) (hlt : ∀ i, i < n → ρ i < n)
    (C : Circuit) (w v : List Bool) (hlen : w.length = v.length)
    (hn : n ≤ w.length) (hrel : wireRel ρ w v) :
    (renameCircuit ρ C).eval v = C.eval w := by
  exact wires_rename ρ n hfix hlt C.gates w v hlen hn hrel C.output

lemma size_rename (ρ : ℕ → ℕ) (C : Circuit) :
    (renameCircuit ρ C).size = C.size := by
  change (C.gates.map (renameGate ρ)).length = C.gates.length
  simp only [List.length_map]

lemma monotone_rename (ρ : ℕ → ℕ) (C : Circuit)
    (hf : Monotone2 C) :
    Monotone2 (renameCircuit ρ C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  obtain ⟨hop, hlen⟩ := hf g' hg'
  exact ⟨hop, by simpa [renameGate] using hlen⟩


def wire (p : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ := if h : i < 14 then (p ⟨i,h⟩).val else i

lemma fixed (p : Equiv.Perm (Fin 14)) (i : ℕ) (hi : 14 ≤ i) : wire p i = i := by simp [wire, Nat.not_lt.mpr hi]

lemma low (p : Equiv.Perm (Fin 14)) (i : ℕ) (hi : i < 14) : wire p i < 14 := by simp [wire,hi]

def act (p : Equiv.Perm (Fin 14)) (i : Fin 15) : Fin 15 :=
  ⟨wire p i.val, by
    by_cases h : i.val < 14
    · have := low p _ h
      omega
    · rw [fixed p _ (by omega)]
      exact i.isLt⟩

lemma act_inj (p : Equiv.Perm (Fin 14)) : Function.Injective (act p) := by
  intro a b hab
  have e : wire p a.val = wire p b.val := congrArg Fin.val hab
  by_cases ha : a.val < 14 <;> by_cases hb : b.val < 14
  · have h : p ⟨a.val,ha⟩ = p ⟨b.val,hb⟩ := Fin.ext (by simpa [wire,ha,hb] using e)
    exact Fin.ext (congrArg (fun i : Fin 14 => i.val) (p.injective h))
  · have := low p _ ha
    rw [fixed p _ (by omega : 14 ≤ b.val)] at e
    omega
  · have := low p _ hb
    rw [fixed p _ (by omega : 14 ≤ a.val)] at e
    omega
  · exact Fin.ext (by simpa [wire,ha,hb] using e)

lemma relInputs (p : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) :
    wireRel (wire p) (List.ofFn (x ∘ p)) (List.ofFn x) := by
  intro i
  by_cases h : i < 14
  · let u : Fin 14 := ⟨i,h⟩
    change (List.ofFn x).getD (wire p i) false = (List.ofFn (x ∘ p)).getD u.val false
    rw [readInput, show wire p i = (p u).val by simp [wire,h,u],readInput]
    rfl
  · rw [fixed p _ (by omega),List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt h),
        List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt h)]

lemma permFeasible {F} {a b : Fin 14} {c d : Fin 15} (h : feasible F a b c d)
    (p : Equiv.Perm (Fin 14)) (hp : ∀ x, F (x ∘ p) = F x) :
    feasible F (min (p a) (p b)) (max (p a) (p b)) (min (act p c) (act p d)) (max (act p c) (act p d)) := by
  obtain ⟨hab,hcd,o,q,D,ho,hq,hm,hs,hx⟩ := h
  refine sortFeasible (o := o) (q := q) (D := renameCircuit (wire p) D)
    (p.injective.ne hab.ne) ((act_inj p).ne hcd.ne) ho hq (monotone_rename _ _ hm) ?_ ?_
  · rwa [size_rename]
  · intro x
    let w := seed (x ∘ p) a b o
    let v := seed x (p a) (p b) o
    have hr : wireRel (wire p) w v := wireRel_append _ 14 (fixed p) (low p) _ _
      (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn,le_refl]) (relInputs p x) _
    have hl : w.length = v.length := by simp only [w,v,seed,List.length_append,List.length_ofFn,List.length_singleton]
    have hn : 14 ≤ w.length := by simp only [w,seed,List.length_append,List.length_ofFn,List.length_singleton]; decide
    have hfinal : wireRel (wire p) (second w c d q) (second v (act p c) (act p d) q) := by
      unfold second
      change wireRel _ _ (v ++ [q.eval [v.getD (wire p c.val) false,v.getD (wire p d.val) false]])
      rw [hr c.val,hr d.val]
      exact wireRel_append _ 14 (fixed p) (low p) _ _ hl hn hr _
    exact (eval_rename _ 14 (fixed p) (low p) D _ _ (by simp only [second,List.length_append,List.length_singleton,hl])
      (by simp only [second,List.length_append,List.length_singleton]; omega) hfinal).trans ((hx (x ∘ p)).trans (hp x))

lemma act_val (p : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (act p i).val = if i < (14 : Fin 15) then (p (Fin.ofNat 14 i.val)).val else 14 := by
  change wire p i.val = _
  by_cases h : i.val < 14
  · rw [ite_eq_left (show i < (14 : Fin 15) from h)]
    simp only [wire,dite_eq_left h]
    congr 2
    exact Fin.ext (by simp [Fin.ofNat,Nat.mod_eq_of_lt h])
  · rw [ite_eq_right (show ¬ i < (14 : Fin 15) from h),fixed p _ (by omega)]
    omega

lemma key_sort (a b : Fin 14) (c d : Fin 15) :
    key (min a b).val (max a b).val (min c d).val (max c d).val = key a.val b.val c.val d.val := by
  rcases le_total a b with h|h <;> rcases le_total c d with j|j <;>
    simp [h,j,key]


end PEqualNP.Outside.L_meta_3322

open PEqualNP.Outside.L_meta_3322

theorem PEqualNP.Outside.L_meta_3322 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro F C hm hn hlo hhi hf
  dsimp only
  let P (k : ℕ) := ∃ (a b : Fin 14) (c d : Fin 15), feasible F a b c d ∧ key a.val b.val c.val d.val = k
  obtain ⟨a,b,c,d,h⟩ := initial C hm hn hlo hhi hf
  have hex : ∃ k, P k := ⟨_,a,b,c,d,h,rfl⟩
  obtain ⟨a,b,c,d,h,hkey⟩ := Nat.find_spec hex
  have least (p : Equiv.Perm (Fin 14)) (hp : ∀ x, F (x ∘ p) = F x) :
      key a.val b.val c.val d.val ≤ key (p a).val (p b).val (act p c).val (act p d).val := by
    rw [hkey]
    exact Nat.find_min' hex ⟨_,_,_,_,permFeasible h p hp,key_sort ..⟩
  obtain ⟨ha,hc,o,q,D,ho,hq,hmD,hs,he⟩ := h
  refine ⟨a,b,c,d,o,q,D,ha,hc,ho,hq,?_,hmD,hs,he⟩
  intro p hp
  simpa only [key,act_val] using least p hp

