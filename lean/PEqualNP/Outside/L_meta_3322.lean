import PEqualNP.Defs

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3322

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def ren (s : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ := if h : i < 14 then (s ⟨i, h⟩ : ℕ) else i

def renG (s : Equiv.Perm (Fin 14)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren s)⟩

theorem ren_lt (s : Equiv.Perm (Fin 14)) (i : ℕ) (h : i < 14) : ren s i < 14 := by
  rw [ren, dif_pos h]; exact (s ⟨i, h⟩).2

theorem ren_ge (s : Equiv.Perm (Fin 14)) (i : ℕ) (h : 14 ≤ i) : ren s i = i := by
  rw [ren, dif_neg (by omega)]

theorem ren_inj (s : Equiv.Perm (Fin 14)) {i j : ℕ} (h : ren s i = ren s j) : i = j := by
  by_cases hi : i < 14 <;> by_cases hj : j < 14
  · rw [ren, ren, dif_pos hi, dif_pos hj] at h
    have := s.injective (Fin.ext h)
    simpa using this
  · have := ren_lt s i hi
    rw [h, ren_ge s j (by omega)] at this
    omega
  · have := ren_lt s j hj
    rw [← h, ren_ge s i (by omega)] at this
    omega
  · rwa [ren_ge s i (by omega), ren_ge s j (by omega)] at h

theorem getD_app (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem run_rel (s : Equiv.Perm (Fin 14)) (gs : List Gate) :
    ∀ x y : List Bool, x.length = y.length → 14 ≤ x.length →
      (∀ i, x.getD i false = y.getD (ren s i) false) →
      ∀ i, (run gs x).getD i false = (run (gs.map (renG s)) y).getD (ren s i) false := by
  induction gs with
  | nil => exact fun x y _ _ h i => h i
  | cons g gs ih =>
    intro x y hl h14 h i
    refine ih _ _ (by simp [hl]) (by simp; omega) (fun k => ?_) i
    have hval : g.op.eval (g.inputs.map fun i => x.getD i false) =
        (renG s g).op.eval ((renG s g).inputs.map fun i => y.getD i false) := by
      simp only [renG, List.map_map]
      congr 1
      exact List.map_congr_left fun a _ => h a
    rw [getD_app, getD_app, hval]
    by_cases hk : k = x.length
    · rw [if_pos hk, if_pos (by rw [ren_ge s k (by omega)]; omega)]
    · rw [if_neg hk, if_neg, h k]
      intro hr
      have : ren s k = ren s x.length := by rw [ren_ge s x.length h14]; omega
      exact hk (ren_inj s this)

theorem ofFn_rel (s : Equiv.Perm (Fin 14)) (z : Fin 14 → Bool) (i : ℕ) :
    (List.ofFn (z ∘ s)).getD i false = (List.ofFn z).getD (ren s i) false := by
  by_cases h : i < 14
  · have h2 := ren_lt s i h
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h2)]
    rw [List.getElem_ofFn, List.getElem_ofFn]
    simp only [Function.comp_apply, ren, h, dif_pos]
  · rw [ren_ge s i (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

theorem eval_ren (s : Equiv.Perm (Fin 14)) (C : Circuit) (z : Fin 14 → Bool) :
    (run (C.gates.map (renG s)) (List.ofFn z)).getD (ren s C.output) false =
      C.eval (List.ofFn (z ∘ s)) :=
  (run_rel s C.gates (List.ofFn (z ∘ s)) (List.ofFn z) (by simp) (by simp)
    (ofFn_rel s z) C.output).symm

def key (a b c d : ℕ) : ℕ :=
  ((15 * min a b + max a b) * 225) + (15 * min c d + max c d)

theorem key_swap1 (a b c d : ℕ) : key b a c d = key a b c d := by
  rw [key, key, min_comm, max_comm]

theorem key_swap2 (a b c d : ℕ) : key a b d c = key a b c d := by
  rw [key, key, min_comm d c, max_comm d c]

theorem op_swap (o : GateOp) (h : o = GateOp.and ∨ o = GateOp.or) (p q : Bool) :
    o.eval [p, q] = o.eval [q, p] := by
  rcases h with rfl | rfl <;> cases p <;> cases q <;> rfl

theorem sorted_pair {a b : ℕ} (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (hne : a ≠ b)
    (u : ℕ → Bool) : o.eval [u (min a b), u (max a b)] = o.eval [u a, u b] := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, op_swap o ho]

theorem main (f : (Fin 14 → Bool) → Bool) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 14 C) (hnd : ∀ g ∈ C.gates, g.inputs.Nodup)
    (h2 : 2 ≤ C.size) (h26 : C.size ≤ 26) (hf : ∀ z : Fin 14 → Bool, C.eval (List.ofFn z) = f z) :
    ∃ (a b : Fin 14) (c d : Fin 15) (o1 o2 : GateOp) (D : Circuit), a < b ∧ c < d ∧
      (o1 = GateOp.and ∨ o1 = GateOp.or) ∧ (o2 = GateOp.and ∨ o2 = GateOp.or) ∧
      (∀ t : Equiv.Perm (Fin 14), (∀ z : Fin 14 → Bool, f (z ∘ t) = f z) →
        key a b c d ≤ key (t a) (t b) (ren t c) (ren t d)) ∧
      PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 24 ∧
      ∀ z : Fin 14 → Bool, D.eval
        ((List.ofFn z ++ [o1.eval [z a, z b]]) ++
          [o2.eval [(List.ofFn z ++ [o1.eval [z a, z b]]).getD c false,
            (List.ofFn z ++ [o1.eval [z a, z b]]).getD d false]]) = f z := by
  classical
  obtain ⟨hops, hback, hlen⟩ := hC
  obtain ⟨gs, out⟩ := C
  match gs, h2 with
  | [], h => simp [Circuit.size] at h
  | [_], h => simp [Circuit.size] at h
  | g1 :: g2 :: rest, _ =>
    have m1 : g1 ∈ (g1 :: g2 :: rest) := by simp
    have m2 : g2 ∈ (g1 :: g2 :: rest) := by simp
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 (hlen g1 m1)
    obtain ⟨r, u, hru⟩ := List.length_eq_two.1 (hlen g2 m2)
    have hpq_ne : p ≠ q := by have := hnd g1 m1; rw [hpq] at this; simpa using this
    have hru_ne : r ≠ u := by have := hnd g2 m2; rw [hru] at this; simpa using this
    have b1 := hback 0 (by simp)
    have b2 := hback 1 (by simp)
    simp only [gateAt, List.getD_cons_zero, List.getD_cons_succ] at b1 b2
    rw [hpq] at b1
    rw [hru] at b2
    have hp : p < 14 := by have := b1 p (by simp); omega
    have hq : q < 14 := by have := b1 q (by simp); omega
    have hr : r < 15 := by have := b2 r (by simp); omega
    have hu : u < 15 := by have := b2 u (by simp); omega
    let aut : Finset (Equiv.Perm (Fin 14)) :=
      Finset.univ.filter fun t => ∀ z : Fin 14 → Bool, f (z ∘ t) = f z
    have haut : aut.Nonempty := ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun z => rfl⟩⟩
    obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image aut
      (fun t => key (ren t p) (ren t q) (ren t r) (ren t u)) haut
    have hsf : ∀ z : Fin 14 → Bool, f (z ∘ s) = f z := (Finset.mem_filter.1 hs).2
    have hne1 : ren s p ≠ ren s q := fun h => hpq_ne (ren_inj s h)
    have hne2 : ren s r ≠ ren s u := fun h => hru_ne (ren_inj s h)
    have hlt15 : ∀ i, i < 15 → ren s i < 15 := by
      intro i hi
      rcases Nat.lt_or_ge i 14 with h | h
      · have := ren_lt s i h; omega
      · rw [ren_ge s i h]; exact hi
    have l1 := ren_lt s p hp
    have l2 := ren_lt s q hq
    have l3 := hlt15 r hr
    have l4 := hlt15 u hu
    have ho1 := hops g1 m1
    have ho2 := hops g2 m2
    refine ⟨⟨min (ren s p) (ren s q), by omega⟩, ⟨max (ren s p) (ren s q), by omega⟩,
      ⟨min (ren s r) (ren s u), by omega⟩, ⟨max (ren s r) (ren s u), by omega⟩, g1.op, g2.op,
      ⟨rest.map (renG s), ren s out⟩, ?_, ?_, ho1, ho2, ?_, ?_, ?_, ?_⟩
    · exact Fin.mk_lt_mk.2 (by omega)
    · exact Fin.mk_lt_mk.2 (by omega)
    · intro t ht
      have hts : (s.trans t) ∈ aut := by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun z => ?_⟩
        have : z ∘ (s.trans t) = (z ∘ t) ∘ s := rfl
        rw [this, hsf, ht]
      have hcomp : ∀ i, ren (s.trans t) i = ren t (ren s i) := by
        intro i
        by_cases h : i < 14
        · have h' := (s ⟨i, h⟩).2
          simp [ren, h]
        · rw [ren_ge _ i (by omega), ren_ge s i (by omega), ren_ge t i (by omega)]
      have hm := hmin _ hts
      simp only [hcomp] at hm
      have hkey : ∀ a b c d : ℕ, key (min a b) (max a b) (min c d) (max c d) = key a b c d := by
        intro a b c d
        simp only [key]
        congr 2 <;> omega
      have hT : ∀ (i : ℕ) (hi : i < 14), ((t ⟨i, hi⟩ : Fin 14) : ℕ) = ren t i := by
        intro i hi; rw [ren, dif_pos hi]
      rw [hT, hT]
      have hk2 : key (ren t (min (ren s p) (ren s q))) (ren t (max (ren s p) (ren s q)))
          (ren t (min (ren s r) (ren s u))) (ren t (max (ren s r) (ren s u))) =
          key (ren t (ren s p)) (ren t (ren s q)) (ren t (ren s r)) (ren t (ren s u)) := by
        rcases le_total (ren s p) (ren s q) with h1 | h1 <;>
          rcases le_total (ren s r) (ren s u) with h3 | h3 <;>
          simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h1, h3, key_swap1,
            key_swap2]
      change key (min (ren s p) (ren s q)) (max (ren s p) (ren s q))
        (min (ren s r) (ren s u)) (max (ren s r) (ren s u)) ≤ _
      rw [hkey]
      exact hm.trans hk2.ge
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      have hm0 : g0 ∈ (g1 :: g2 :: rest) := by simp [hg0]
      refine ⟨?_, ?_⟩
      · rcases hops g0 hm0 with h | h <;> simp [renG, h]
      · have := hlen g0 hm0
        simp [renG, this]
    · simp only [Circuit.size, List.length_cons, List.length_map] at h26 ⊢
      omega
    · intro z
      have hE := eval_ren s ⟨g1 :: g2 :: rest, out⟩ z
      rw [hf, hsf] at hE
      rw [← hE]
      have e1 : (renG s g1).op.eval ((renG s g1).inputs.map fun i => (List.ofFn z).getD i false) =
          g1.op.eval [z ⟨min (ren s p) (ren s q), by omega⟩,
            z ⟨max (ren s p) (ren s q), by omega⟩] := by
        have hz : ∀ (i : ℕ) (hi : i < 14), z ⟨i, hi⟩ = (List.ofFn z).getD i false := by
          intro i hi
          rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
        rw [hz, hz, sorted_pair g1.op ho1 hne1 (fun i => (List.ofFn z).getD i false)]
        simp [renG, hpq]
      have e2 : ∀ l : List Bool,
          (renG s g2).op.eval ((renG s g2).inputs.map fun i => l.getD i false) =
          g2.op.eval [l.getD (min (ren s r) (ren s u)) false,
            l.getD (max (ren s r) (ren s u)) false] := by
        intro l
        rw [sorted_pair g2.op ho2 hne2 (fun i => l.getD i false)]
        simp [renG, hru]
      change (run (rest.map (renG s)) _).getD (ren s out) false =
        (run (rest.map (renG s))
          ((List.ofFn z ++ [(renG s g1).op.eval ((renG s g1).inputs.map fun i =>
            (List.ofFn z).getD i false)]) ++ [(renG s g2).op.eval ((renG s g2).inputs.map fun i =>
              (List.ofFn z ++ [(renG s g1).op.eval ((renG s g1).inputs.map fun i =>
                (List.ofFn z).getD i false)]).getD i false)])).getD (ren s out) false
      rw [e1, e2]

end PEqualNP.Outside.L_meta_3322

theorem PEqualNP.Outside.L_meta_3322 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  intro f C hC hnd h2 h26 hf
  obtain ⟨a, b, c, d, o1, o2, D, hab, hcd, ho1, ho2, hmin, hD, hDs, hDe⟩ :=
    PEqualNP.Outside.L_meta_3322.main f C hC hnd h2 h26 hf
  refine ⟨a, b, c, d, o1, o2, D, hab, hcd, ho1, ho2, ?_, hD, hDs, hDe⟩
  intro t ht
  have hr : ∀ e : Fin 15, (if e < (14 : Fin 15) then ((t (Fin.ofNat 14 (e : ℕ)) : Fin 14) : ℕ)
      else 14) = PEqualNP.Outside.L_meta_3322.ren t e := by
    intro e
    by_cases h : (e : ℕ) < 14
    · have h' : e < (14 : Fin 15) := h
      rw [if_pos h', PEqualNP.Outside.L_meta_3322.ren, dif_pos h]
      congr 2
      exact Fin.ext (Nat.mod_eq_of_lt h)
    · have h' : ¬ e < (14 : Fin 15) := h
      rw [if_neg h', PEqualNP.Outside.L_meta_3322.ren, dif_neg h]
      omega
  have := hmin t ht
  simp only [hr]
  exact this