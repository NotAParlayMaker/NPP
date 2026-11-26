import Mathlib.Data.Finset.Card
import PEqualNP.Defs

-- Submitted via OpenAI Codex by gpt-6.2-astra.
-- The reader sets and graph encoding follow upstream R_meta_6768_219.

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_6766_836
    (wires : ∀ (C : Circuit), IsAO2 11 C →
      (∀ (v : Fin 11) (x : Fin 11 → Bool), wval C x v.val = x v) ∧
      ∀ j < C.size, ∃ p q : ℕ, p < 11+j ∧ q < 11+j ∧ (gateAt C j).inputs = [p,q] ∧
        ∀ x : Fin 11 → Bool,
          ((gateAt C j).op = GateOp.and → wval C x (11+j) = (wval C x p && wval C x q)) ∧
          ((gateAt C j).op ≠ GateOp.and → wval C x (11+j) = (wval C x p || wval C x q)))
    (rest : let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map (fun t => (t/11,t%11)))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
        2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2*(Ustar G C).card →
        (∀ z : Fin 11, z.val < 4 → (readers 0 C z.val).card ≤ 2) →
        ∀ (v : Fin 11) (a b : ℕ), v.val < 4 → a < b → b < C.size →
          (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.or →
          readers 0 C v.val = {a} → readers 11 C a = {b} →
          ∃ (z : Fin 11) (J : Finset ℕ), z.val < 4 ∧ (if z = v then 1 else 3) ≤ J.card ∧
            ∀ j ∈ J, j < C.size ∧ (z = v → j ≠ a ∧ j ≠ b) ∧
              ∃ k < 11+j, ∀ x : Fin 11 → Bool, x z = false → wval C x (11+j) = wval C x k) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             ∀ (x8 : Fin (11 : ℕ)) (x9 x10 : ℕ),               ↑x8 < (4 : ℕ) →                 x9 < x10 →                   x10 < x2.size →                     (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and →                       (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or →                         (∀ x16 < x2.size, ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = x9) →                           (∀ x17 < x2.size, (11 : ℕ) + x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x17).inputs ↔ x17 = x10) →                             ∃ (x18 : Fin (11 : ℕ)),                               ↑x18 < (4 : ℕ) ∧                                 have x19 : ℕ → Prop := fun (x19 : ℕ) => ∃ x20 < (11 : ℕ) + x19, ∀ (x21 : Fin (11 : ℕ) → Bool), x21 x18 = Bool.false → PEqualNP.ReadTwo.wval x2 x21 ((11 : ℕ) + x19) = PEqualNP.ReadTwo.wval x2 x21 x20;                                 ∃ (x20 : ℕ) (x21 : ℕ) (x22 : ℕ), x20 < x21 ∧ x21 < x22 ∧ x22 < x2.size ∧ x19 x20 ∧ x19 x21 ∧ x19 x22 := by
  classical
  intro G C minC htop hj hs hd v a b hv hab hbs haOp hbOp haRead hbRead
  have has : a < C.size := by omega
  obtain ⟨base, spec⟩ := wires C minC.1
  let dup (z : Fin 11) (j : ℕ) := ∃ k < 11+j, ∀ x : Fin 11 → Bool,
    x z = false → wval C x (11+j) = wval C x k
  have finish (z : Fin 11) (hz : z.val < 4) (J : Finset ℕ) (hJ : 3 ≤ J.card)
      (valid : ∀ j ∈ J, j < C.size ∧ dup z j) :
      ∃ z : Fin 11, z.val < 4 ∧ ∃ i j k, i < j ∧ j < k ∧ k < C.size ∧ dup z i ∧ dup z j ∧ dup z k := by
    obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩ := Finset.two_lt_card_iff.mp hJ
    obtain ⟨ps, pd⟩ := valid p hp
    obtain ⟨qs, qd⟩ := valid q hq
    obtain ⟨rs, rd⟩ := valid r hr
    refine ⟨z, hz, ?_⟩
    rcases lt_or_gt_of_ne hpq with h | h <;> rcases lt_or_gt_of_ne hpr with g | g <;>
      rcases lt_or_gt_of_ne hqr with f | f <;>
      first | exact ⟨p,q,r,h,f,rs,pd,qd,rd⟩ | exact ⟨p,r,q,g,f,qs,pd,rd,qd⟩
            | exact ⟨q,p,r,h,g,rs,qd,pd,rd⟩ | exact ⟨q,r,p,f,g,ps,qd,rd,pd⟩
            | exact ⟨r,p,q,g,h,qs,rd,pd,qd⟩ | exact ⟨r,q,p,f,h,ps,rd,qd,pd⟩ | omega
  have memR (n i j : ℕ) : j ∈ readers n C i ↔ j < C.size ∧ n+i ∈ (gateAt C j).inputs := by
    change j ∈ (Finset.range C.gates.length).filter (fun k => n+i ∈ (gateAt C k).inputs) ↔ _
    rw [Finset.mem_filter, Finset.mem_range]
    rfl
  have foldGate (z : Fin 11) (j w : ℕ) (hj : j < C.size) (hm : w ∈ (gateAt C j).inputs)
      (zero : ∀ x : Fin 11 → Bool, x z = false → wval C x w = false) : dup z j := by
    obtain ⟨p,q,hp,hq,hin,he⟩ := spec j hj
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    by_cases op : (gateAt C j).op = GateOp.and
    · refine ⟨z.val, by have := z.isLt; omega, ?_⟩
      intro x hx
      rcases hm with rfl | rfl <;> simp [(he x).1 op, zero x hx, base, hx]
    · rcases hm with rfl | rfl
      · exact ⟨q, hq, fun x hx => by simp [(he x).2 op, zero x hx]⟩
      · exact ⟨p, hp, fun x hx => by simp [(he x).2 op, zero x hx]⟩
  by_cases sparse : ∀ z : Fin 11, z.val < 4 → (readers 0 C z.val).card ≤ 2
  · have readA : readers 0 C v.val = {a} := by
      ext j
      rw [memR]
      simp only [Nat.zero_add, Finset.mem_singleton]
      exact ⟨fun h => (haRead j h.1).1 h.2, fun h => h ▸ ⟨has, (haRead a has).2 rfl⟩⟩
    have readB : readers 11 C a = {b} := by
      ext j
      rw [memR]
      simp only [Finset.mem_singleton]
      exact ⟨fun h => (hbRead j h.1).1 h.2, fun h => h ▸ ⟨hbs, (hbRead b hbs).2 rfl⟩⟩
    obtain ⟨z,J,hz,hJ,hvalid⟩ := rest C minC htop hj hs hd sparse v a b hv hab hbs haOp hbOp readA readB
    by_cases eqz : z = v
    · subst z
      simp only [ite_true] at hJ
      have mA := (haRead a has).2 rfl
      have zeroA : ∀ x : Fin 11 → Bool, x v = false → wval C x (11+a) = false := by
        obtain ⟨p,q,_,_,hin,he⟩ := spec a has
        rw [hin] at mA
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mA
        intro x hx
        rcases mA with hp | hq
        · simp [(he x).1 haOp, ← hp, base, hx]
        · simp [(he x).1 haOp, ← hq, base, hx]
      have da := foldGate v a v.val has ((haRead a has).2 rfl) (fun x hx => (base v x).trans hx)
      have db := foldGate v b (11+a) hbs ((hbRead b hbs).2 rfl) zeroA
      obtain ⟨k,hk⟩ := Finset.card_pos.mp hJ
      obtain ⟨ks, nk, dk⟩ := hvalid k hk
      obtain ⟨ka,kb⟩ := nk rfl
      apply finish v hv {a,b,k}
      · have ab : a ≠ b := by omega
        simp [ab, Ne.symm ka, Ne.symm kb]
      · intro j h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl
        · exact ⟨has, da⟩
        · exact ⟨hbs, db⟩
        · exact ⟨ks, dk⟩
    · simp only [ite_eq_right eqz] at hJ
      exact finish z hz J hJ (fun j h => ⟨(hvalid j h).1,(hvalid j h).2.2⟩)
  · push Not at sparse
    obtain ⟨z,hz,hc⟩ := sparse
    apply finish z hz (readers 0 C z.val) hc
    intro j h
    obtain ⟨js, hm⟩ := (memR 0 z.val j).1 h
    rw [Nat.zero_add] at hm
    exact ⟨js, foldGate z j z.val js hm (fun x hx => (base z x).trans hx)⟩
