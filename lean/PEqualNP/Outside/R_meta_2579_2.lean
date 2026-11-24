import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- Take a cut retaining at least half the residual edges, then remove low-degree vertices.
theorem PEqualNP.Outside.R_meta_2579_2
    (supportBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), IsLeastAO G C →
      G.support.ncard ≤ C.size + 1)
    (coreBound : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ K : Finset (Sym2 (Fin n)),
      K ⊆ ((Ustar G C).filter (fun e => ¬ ∃ u v : Fin n, e = s(u, v) ∧
        ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n + h)).card ∧
          (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v})) →
      (∃ c : Fin n → Bool, ∀ e ∈ K, ¬ (e.map c).IsDiag) →
      (∀ v : Fin n, (∃ e ∈ K, v ∈ e) → 3 ≤ (K.filter (fun e => v ∈ e)).card) →
      K.card ≤ k * (C.size + 1)) :
    ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ¬ ∃ u v : Fin n, e = s(u, v) ∧
        ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n + h)).card ∧
          (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v})).card ≤ k * (C.size + 1) := by
  classical
  have cutBound (n : ℕ) (F : Finset (Sym2 (Fin n))) (loopless : ∀ e ∈ F, ¬ e.IsDiag) :
      ∃ c : Fin n → Bool, F.card ≤ 2 * (F.filter (fun e => ¬ (e.map c).IsDiag)).card := by
    let colors : Finset (Fin n → Bool) := Finset.univ
    have half (e : Sym2 (Fin n)) (he : e ∈ F) :
        2 * (colors.filter (fun c => ¬ (e.map c).IsDiag)).card = colors.card := by
      induction e using Sym2.inductionOn with
      | _ a b =>
        have ne : a ≠ b := by simpa using loopless _ he
        let flip (c : Fin n → Bool) := Function.update c a (!c a)
        have atA (c) : flip c a = !c a := by simp [flip]
        have atB (c) : flip c b = c b := by simp [flip,ne.symm]
        have inv (c) : flip (flip c) = c := by
          funext i
          by_cases eq : i = a <;> simp [eq,flip,Function.update_of_ne]
        have eqCard : (colors.filter (fun c => c a = c b)).card =
            (colors.filter (fun c => c a ≠ c b)).card := by
          apply Finset.card_bij' (fun c _ => flip c) (fun c _ => flip c)
          · intro c hc
            have eq := (Finset.mem_filter.mp hc).2
            simp [colors,atA,atB,eq]
          · intro c hc
            have ne' := (Finset.mem_filter.mp hc).2
            have eq : (!c a) = c b := by cases h : c a <;> cases h' : c b <;> simp_all
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (atA c).trans (eq.trans (atB c).symm)⟩
          · exact fun c _ => inv c
          · exact fun c _ => inv c
        have partition := Finset.card_filter_add_card_filter_not (s := colors) (fun c => c a = c b)
        change 2 * (colors.filter (fun c => c a ≠ c b)).card = colors.card
        rw [eqCard] at partition
        simpa only [two_mul] using partition
    by_contra! small
    have pos : 0 < colors.card := Finset.card_pos.mpr ⟨fun _ => false,Finset.mem_univ _⟩
    have sumsmall : ∑ c ∈ colors, 2 * (F.filter (fun e => ¬ (e.map c).IsDiag)).card <
        ∑ _c ∈ colors, F.card :=
      Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp pos) (fun c _ => small c)
    have swap : ∑ c ∈ colors, 2 * (F.filter (fun e => ¬ (e.map c).IsDiag)).card =
        ∑ e ∈ F, 2 * (colors.filter (fun c => ¬ (e.map c).IsDiag)).card := by
      simp only [Finset.card_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [swap, Finset.sum_congr rfl half] at sumsmall
    simp [Nat.mul_comm] at sumsmall
  obtain ⟨k, core⟩ := coreBound
  refine ⟨2*k + 4, ?_⟩
  intro n G _ girth edge C least top
  let R := ((Ustar G C).filter (fun e => ¬ ∃ u v : Fin n, e = s(u, v) ∧
        ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n + h)).card ∧
          (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v}))
  let V := Finset.univ.filter (fun v => ∃ w, G.Adj v w)
  obtain ⟨c,hcut⟩ := cutBound n R (by
    intro e he
    have hedge : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp hedge))
  let cut := R.filter (fun e => ¬ (e.map c).IsDiag)
  have peel (S : Finset (Fin n)) : ∀ F : Finset (Sym2 (Fin n)), F ⊆ cut →
      (∀ e ∈ F, ∀ v ∈ e, v ∈ S) → F.card ≤ k * (C.size + 1) + 2 * S.card := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro F sub inside
      by_cases kernel : ∀ v : Fin n, (∃ e ∈ F, v ∈ e) → 3 ≤ (F.filter (fun e => v ∈ e)).card
      · have bound := core n G girth edge C least top F (sub.trans (Finset.filter_subset _ _))
          ⟨c,fun e he => (Finset.mem_filter.mp (sub he)).2⟩ kernel
        omega
      · push Not at kernel
        obtain ⟨v, ⟨e, he, hv⟩, low⟩ := kernel
        have mem := inside e he v hv
        let keep := F.filter (fun a => v ∉ a)
        have keepSub : keep ⊆ F := Finset.filter_subset _ _
        have small := ih (S.erase v) (Finset.erase_ssubset mem) keep (keepSub.trans sub) (by
          intro a ha u hu
          obtain ⟨ha',absent⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_erase.mpr ⟨fun eqn => absent (eqn ▸ hu),inside a ha' u hu⟩)
        have partition := Finset.card_filter_add_card_filter_not (s := F) (fun a => v ∈ a)
        change _ + keep.card = F.card at partition
        rw [Finset.card_erase_of_mem mem] at small
        have positive := Finset.card_pos.mpr ⟨v,mem⟩
        omega
  have bound := peel V cut (fun _ h => h) (by
    intro e he v hv
    have inR : e ∈ R := (Finset.mem_filter.mp he).1
    have hedge : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp (Finset.mem_filter.mp inR).1).1
    induction e using Sym2.inductionOn with
    | _ a b =>
      have adj := SimpleGraph.mem_edgeFinset.mp hedge
      rcases Sym2.mem_iff.mp hv with rfl|rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,adj⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,adj.symm⟩)
  have eqSupport : (V : Set (Fin n)) = G.support := by ext v; simp [V,SimpleGraph.mem_support]
  have vs := supportBound n G C least
  rw [← eqSupport,Set.ncard_coe_finset] at vs
  change R.card ≤ 2*cut.card at hcut
  change R.card ≤ _
  simp only [Nat.add_mul,Nat.mul_assoc]
  omega
