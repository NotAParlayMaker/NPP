import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4081_1
    (coverCounting : ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
      (U : Finset α) (J : Finset β) (fiber : β → Finset α),
      (∀ e ∈ U, ∃ h ∈ J, e ∈ fiber h) →
      U.card ≤ ∑ h ∈ J, (fiber h).card)
    (junkFiberBudget :
      let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
        (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10),
        (7, 9), (8, 9)]
      ∀ D : Circuit, D.size ≤ 21 → IsLeastAO G D → TopForm G D →
        3 ≤ (junk G D).card →
        (∀ u v : Fin 11, s(u, v) ∈ Ustar G D →
          ∃ h ∈ junk G D, gateVal 11 D h (pairInput u v) = true) →
        3 ≤ (Ustar G D).card →
        2 * (centreless G D).card + (junk G D).card +
          (orN G D \ lam G D).card < 2 * (Ustar G D).card →
        (∑ h ∈ junk G D,
          ((Ustar G D).filter (fun e =>
            ∃ u v : Fin 11, e = s(u, v) ∧
              gateVal 11 D h (pairInput u v) = true)).card) ≤
          (junk G D).card + 2 * (centreless G D).card +
            (orN G D \ lam G D).card) :
    let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
      (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10),
      (7, 9), (8, 9)]
    ∀ D : Circuit, D.size ≤ 21 → IsLeastAO G D → TopForm G D →
      3 ≤ (junk G D).card →
      (∀ u v : Fin 11, s(u, v) ∈ Ustar G D →
        ∃ h ∈ junk G D, gateVal 11 D h (pairInput u v) = true) →
      3 ≤ (Ustar G D).card →
      2 * (centreless G D).card + (junk G D).card +
        (orN G D \ lam G D).card < 2 * (Ustar G D).card →
      (Ustar G D).card ≤
        2 * (centreless G D).card + (junk G D).card +
          (orN G D \ lam G D).card := by
  intro G
  intro D hsize hleast htop hjunk hcover hU hstrict
  let U := Ustar G D
  let J := junk G D
  let fiber : ℕ → Finset (Sym2 (Fin 11)) := fun h =>
    U.filter (fun e => ∃ u v : Fin 11, e = s(u, v) ∧
      gateVal 11 D h (pairInput u v) = true)
  have hcovered : ∀ e ∈ U, ∃ h ∈ J, e ∈ fiber h := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
        have he' : s(u, v) ∈ U := by simpa using he
        obtain ⟨h, hh, hv⟩ := hcover u v he'
        refine ⟨h, hh, ?_⟩
        simp only [fiber, Finset.mem_filter]
        exact ⟨he', ⟨u, v, rfl, hv⟩⟩
  have hcount := coverCounting U J fiber hcovered
  have hbudget := junkFiberBudget D hsize hleast htop hjunk hcover hU hstrict
  change U.card ≤
    2 * (centreless G D).card + J.card + (orN G D \ lam G D).card
  change U.card ≤ ∑ h ∈ J, (fiber h).card at hcount
  change (∑ h ∈ J, (fiber h).card) ≤
    J.card + 2 * (centreless G D).card + (orN G D \ lam G D).card at hbudget
  omega
