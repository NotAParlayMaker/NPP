import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.HeptadCover

set_option maxRecDepth 24000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2600_1
    (hTop : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b : Fin 26, G.Adj a b ↔
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
           (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      IsLeastAO G C →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size = C.size ∧
        52 + (tops G D \ centreless G D).card + 2 * (centreless G D).card +
          (junk G D).card + (orN G D \ lam G D).card ≤ D.size + (Ustar G D).card + 1 ∧
        ∀ K : Finset (Fin 26), IsMinCover (G.deleteEdges ↑(Ustar G D)) K →
          K.card ≤ (tops G D \ centreless G D).card)
    (hJunk1 : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (D : Circuit),
      (∀ a b : Fin 26, G.Adj a b ↔
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
           (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      IsLeastAO G D → TopForm G D → D.size ≤ 62 →
      (junk G D).card = 1 → 4 ≤ (Ustar G D).card →
      8 + 8 * (centreless G D).card + 4 * (junk G D).card +
        4 * (orN G D \ lam G D).card ≤ 5 * (Ustar G D).card → False)
    (hJunk2NoC : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (D : Circuit),
      (∀ a b : Fin 26, G.Adj a b ↔
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
           (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      IsLeastAO G D → TopForm G D → D.size ≤ 62 →
      2 ≤ (junk G D).card → centreless G D = ∅ →
      5 ≤ (Ustar G D).card → 1 ≤ (orN G D \ lam G D).card →
      8 + 4 * (junk G D).card + 4 * (orN G D \ lam G D).card ≤
        5 * (Ustar G D).card → False)
    (hJunk2WithC : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (D : Circuit),
      (∀ a b : Fin 26, G.Adj a b ↔
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
           (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      IsLeastAO G D → TopForm G D → D.size ≤ 62 →
      2 ≤ (junk G D).card → 1 ≤ (centreless G D).card →
      5 ≤ (Ustar G D).card →
      8 + 8 * (centreless G D).card + 4 * (junk G D).card +
        4 * (orN G D \ lam G D).card ≤ 5 * (Ustar G D).card → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  intro C hwf heval
  by_contra hlt
  have hCsize : C.size ≤ 62 := by omega
  let adj3 : Fin 26 → Fin 26 → Prop := fun a b =>
    ∃ p l : Fin 13, p ∈ singerLines3 l ∧
      ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
       (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))
  let G3 : SimpleGraph (Fin 26) :=
    { Adj := adj3
      symm := ⟨by
        rintro a b ⟨p, l, hpl, hor⟩
        exact ⟨p, l, hpl, hor.symm⟩⟩
      loopless := ⟨by
        rintro a ⟨p, l, _, hor⟩
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hv := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        · have hv := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega⟩ }
  have hG3 : ∀ a b : Fin 26, G3.Adj a b ↔
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) := fun _ _ => Iff.rfl
  have hsinger_iff : ∀ u t : Fin 13,
      (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ↔ u ∈ singerLines3 t := by decide
  have hcast_ne_nat : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro p l h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hcast_inj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := fun a b h =>
    Fin.ext (by simpa using congrArg Fin.val h)
  have hnat_inj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := fun a b h =>
    Fin.ext (by have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; omega)
  have hadj_cast_nat : ∀ p l : Fin 13,
      G3.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) ↔ p ∈ singerLines3 l := by
    intro p l
    constructor
    · rintro ⟨p', l', hpl, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · have hp : p = p' := hcast_inj h1
        have hl : l = l' := hnat_inj h2
        rw [hp, hl]; exact hpl
      · exact (hcast_ne_nat p l' h2).elim
    · intro hpl
      exact ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩
  have hG3_deg_pt : ∀ p : Fin 13, (Finset.univ.filter fun l : Fin 13 => p ∈ singerLines3 l).card = 4 := by
    decide
  have hG3_deg_ln : ∀ l : Fin 13, (singerLines3 l).card = 4 := by decide
  have hG3_4free_pt : ∀ p1 p2 : Fin 13, p1 ≠ p2 →
      (Finset.univ.filter fun l : Fin 13 => p1 ∈ singerLines3 l ∧ p2 ∈ singerLines3 l).card ≤ 1 := by
    decide
  have hG3_4free_ln : ∀ l1 l2 : Fin 13, l1 ≠ l2 → (singerLines3 l1 ∩ singerLines3 l2).card ≤ 1 := by
    decide
  have hmiss_p1 : ∀ p : Fin 13,
      (Finset.univ.filter fun l : Fin 13 => p ∉ singerLines3 l).card = 9 := by decide
  have hmiss_p2 : ∀ p1 p2 : Fin 13, p1 ≠ p2 →
      (Finset.univ.filter fun l : Fin 13 => p1 ∉ singerLines3 l ∧ p2 ∉ singerLines3 l).card = 6 := by
    decide
  have hmiss_p3 : ∀ p1 p2 p3 : Fin 13, p1 ≠ p2 → p1 ≠ p3 → p2 ≠ p3 →
      (Finset.univ.filter fun l : Fin 13 =>
        p1 ∉ singerLines3 l ∧ p2 ∉ singerLines3 l ∧ p3 ∉ singerLines3 l).card ≤ 4 := by decide
  have hmiss_l1 : ∀ l : Fin 13,
      (Finset.univ.filter fun p : Fin 13 => p ∉ singerLines3 l).card = 9 := by decide
  have hmiss_l2 : ∀ l1 l2 : Fin 13, l1 ≠ l2 →
      (Finset.univ.filter fun p : Fin 13 => p ∉ singerLines3 l1 ∧ p ∉ singerLines3 l2).card = 6 := by
    decide
  have hmiss_l3 : ∀ l1 l2 l3 : Fin 13, l1 ≠ l2 → l1 ≠ l3 → l2 ≠ l3 →
      (Finset.univ.filter fun p : Fin 13 =>
        p ∉ singerLines3 l1 ∧ p ∉ singerLines3 l2 ∧ p ∉ singerLines3 l3).card ≤ 4 := by decide
  have hG3_4free : NoFourCycle G3 := by
    intro a b hab
    by_cases ha : a.val < 13 <;> by_cases hb : b.val < 13
    · let p1 : Fin 13 := ⟨a.val, ha⟩
      let p2 : Fin 13 := ⟨b.val, hb⟩
      have hae : a = Fin.castAdd 13 p1 := Fin.ext rfl
      have hbe : b = Fin.castAdd 13 p2 := Fin.ext rfl
      have hne : p1 ≠ p2 := fun h => hab (by rw [hae, hbe, h])
      have hsub : (Finset.univ.filter fun w : Fin 26 => G3.Adj a w ∧ G3.Adj b w) ⊆
          (Finset.univ.filter fun l : Fin 13 => p1 ∈ singerLines3 l ∧ p2 ∈ singerLines3 l).image
            (Fin.natAdd 13) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨u, l, hpl, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hw.1
        · subst h2
          rw [hae] at h1
          have hp1 : p1 = u := hcast_inj h1
          rw [hbe, hadj_cast_nat] at hw
          exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1 ▸ hpl, hw.2⟩, rfl⟩
        · rw [hae] at h2
          exact (hcast_ne_nat p1 l h2).elim
      exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (hG3_4free_pt p1 p2 hne))
    · have hemp : (Finset.univ.filter fun w : Fin 26 => G3.Adj a w ∧ G3.Adj b w) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨p1, l1, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hw.1
        · obtain ⟨p2, l2, _, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ := hw.2
          · have hv := congrArg Fin.val h3; simp only [Fin.val_castAdd] at hv; omega
          · have hv := congrArg Fin.val (h2.symm.trans h3)
            simp only [Fin.val_natAdd, Fin.val_castAdd] at hv; omega
        · have hv := congrArg Fin.val h2; simp only [Fin.val_natAdd] at hv; omega
      rw [hemp]; simp
    · have hemp : (Finset.univ.filter fun w : Fin 26 => G3.Adj a w ∧ G3.Adj b w) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨p1, l1, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hw.1
        · have hv := congrArg Fin.val h1; simp only [Fin.val_castAdd] at hv; omega
        · obtain ⟨p2, l2, _, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ := hw.2
          · have hv := congrArg Fin.val (h1.symm.trans h4)
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
          · have hv := congrArg Fin.val h4; simp only [Fin.val_natAdd] at hv; omega
      rw [hemp]; simp
    · let l1 : Fin 13 := ⟨a.val - 13, by omega⟩
      let l2 : Fin 13 := ⟨b.val - 13, by omega⟩
      have hae : a = Fin.natAdd 13 l1 := Fin.ext (by dsimp [l1]; omega)
      have hbe : b = Fin.natAdd 13 l2 := Fin.ext (by dsimp [l2]; omega)
      have hne : l1 ≠ l2 := fun h => hab (by rw [hae, hbe, h])
      have hsub : (Finset.univ.filter fun w : Fin 26 => G3.Adj a w ∧ G3.Adj b w) ⊆
          (singerLines3 l1 ∩ singerLines3 l2).image (Fin.castAdd 13) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨p, t, hpt, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hw.1
        · rw [hae] at h1
          exact (hcast_ne_nat p l1 h1.symm).elim
        · subst h1
          rw [hae] at h2
          have hl1 : l1 = t := hnat_inj h2
          have h2' : G3.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l2) := hbe ▸ hw.2.symm
          rw [hadj_cast_nat] at h2'
          exact Finset.mem_image.mpr ⟨p, Finset.mem_inter.mpr ⟨hl1 ▸ hpt, h2'⟩, rfl⟩
      exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (hG3_4free_ln l1 l2 hne))
  have hG3_edges_eq : G3.edgeFinset =
      ((Finset.univ : Finset (Fin 13 × Fin 13)).filter fun q => q.1 ∈ singerLines3 q.2).image
        (fun q => s(Fin.castAdd 13 q.1, Fin.natAdd 13 q.2)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨(p, l), hpl, rfl⟩
        · exact ⟨(p, l), hpl, Sym2.eq_swap⟩
      · rintro ⟨⟨p, l⟩, hpl, heq⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨p, l, hpl, Or.inl ⟨h1.symm, h2.symm⟩⟩
        · exact ⟨p, l, hpl, Or.inr ⟨h1.symm, h2.symm⟩⟩
  have hG3_card : G3.edgeFinset.card = 52 := by
    rw [hG3_edges_eq, Finset.card_image_of_injOn]
    · decide
    · rintro ⟨p1, l1⟩ _ ⟨p2, l2⟩ _ heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext (hcast_inj h1) (hnat_inj h2)
      · exact (hcast_ne_nat p1 l2 h1).elim
  let inc (v : Fin 26) : Finset (Sym2 (Fin 26)) := G3.edgeFinset.filter (fun e => v ∈ e)
  have hinc_card : ∀ v : Fin 26, (inc v).card = 4 := by
    intro v
    by_cases hv : v.val < 13
    · let p : Fin 13 := ⟨v.val, hv⟩
      have hve : v = Fin.castAdd 13 p := Fin.ext rfl
      have heq : inc v = (Finset.univ.filter fun l : Fin 13 => p ∈ singerLines3 l).image
          (fun l => s(Fin.castAdd 13 p, Fin.natAdd 13 l)) := by
        ext e
        induction e using Sym2.ind with
        | _ a b =>
          simp only [inc, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            Sym2.mem_iff, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨p', l', hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hmem⟩
            · rcases hmem with h1 | h1
              · rw [hve] at h1
                have hp : p = p' := hcast_inj h1
                exact ⟨l', hp ▸ hpl, by rw [hp]⟩
              · rw [hve] at h1; exact (hcast_ne_nat p l' h1).elim
            · rcases hmem with h1 | h1
              · rw [hve] at h1; exact (hcast_ne_nat p l' h1).elim
              · rw [hve] at h1
                have hp : p = p' := hcast_inj h1
                exact ⟨l', hp ▸ hpl, by rw [hp]; exact Sym2.eq_swap⟩
          · rintro ⟨l, hpl, heq⟩
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩, Or.inl hve⟩
            · exact ⟨⟨p, l, hpl, Or.inr ⟨rfl, rfl⟩⟩, Or.inr hve⟩
      rw [heq, Finset.card_image_of_injOn]
      · exact hG3_deg_pt p
      · intro l1 _ l2 _ h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hnat_inj h2
        · exact (hcast_ne_nat p l2 h1).elim
    · let l : Fin 13 := ⟨v.val - 13, by omega⟩
      have hve : v = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      have heq : inc v = (singerLines3 l).image (fun p => s(Fin.castAdd 13 p, Fin.natAdd 13 l)) := by
        ext e
        induction e using Sym2.ind with
        | _ a b =>
          simp only [inc, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            Sym2.mem_iff, Finset.mem_image]
          constructor
          · rintro ⟨⟨p', l', hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hmem⟩
            · rcases hmem with h1 | h1
              · rw [hve] at h1; exact (hcast_ne_nat p' l h1.symm).elim
              · rw [hve] at h1
                have hl : l = l' := hnat_inj h1
                exact ⟨p', hl ▸ hpl, by rw [hl]⟩
            · rcases hmem with h1 | h1
              · rw [hve] at h1
                have hl : l = l' := hnat_inj h1
                exact ⟨p', hl ▸ hpl, by rw [hl]; exact Sym2.eq_swap⟩
              · rw [hve] at h1; exact (hcast_ne_nat p' l h1.symm).elim
          · rintro ⟨p, hpl, heq⟩
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩, Or.inr hve⟩
            · exact ⟨⟨p, l, hpl, Or.inr ⟨rfl, rfl⟩⟩, Or.inl hve⟩
      rw [heq, Finset.card_image_of_injOn]
      · exact hG3_deg_ln l
      · intro p1 _ p2 _ h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hcast_inj h1
        · exact (hcast_ne_nat p1 l h1).elim
  have hCoverBound : ∀ (U : Finset (Sym2 (Fin 26))) (K : Finset (Fin 26)),
      (G3.deleteEdges ↑U).IsVertexCover (K : Set (Fin 26)) → 52 ≤ 4 * K.card + U.card := by
    intro U K hK
    have hsub : G3.edgeFinset \ U ⊆ K.biUnion inc := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        have hadj : (G3.deleteEdges ↑U).Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨he.1, he.2⟩
        rcases hK hadj with ha | hb
        · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr
            ⟨SimpleGraph.mem_edgeFinset.mpr he.1, Sym2.mem_mk_left a b⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr
            ⟨SimpleGraph.mem_edgeFinset.mpr he.1, Sym2.mem_mk_right a b⟩⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 : (K.biUnion inc).card ≤ ∑ v ∈ K, (inc v).card := Finset.card_biUnion_le
    have hsum : ∑ v ∈ K, (inc v).card = 4 * K.card := by
      simp only [hinc_card, Finset.sum_const, smul_eq_mul, mul_comm]
    have hsdiff : G3.edgeFinset.card ≤ (G3.edgeFinset \ U).card + U.card := by
      have := Finset.card_sdiff_add_card_inter G3.edgeFinset U
      have := Finset.card_le_card (Finset.inter_subset_right (s₁ := G3.edgeFinset) (s₂ := U))
      omega
    omega
  have hindep12 : ∀ K : Finset (Fin 26), K.card = 12 →
      (∀ u ∈ K, ∀ v ∈ K, ¬ G3.Adj u v) →
      (∀ v ∈ K, v.val < 13) ∨ (∀ v ∈ K, 13 ≤ v.val) := by
    intro K hKcard hindep
    let P : Finset (Fin 13) := Finset.univ.filter fun p => Fin.castAdd 13 p ∈ K
    let L : Finset (Fin 13) := Finset.univ.filter fun l => Fin.natAdd 13 l ∈ K
    have hKeq : K = P.image (Fin.castAdd 13) ∪ L.image (Fin.natAdd 13) := by
      ext v
      simp only [Finset.mem_union, Finset.mem_image, P, L, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · intro hv
        by_cases h13 : v.val < 13
        · left
          exact ⟨⟨v.val, h13⟩, by rwa [show Fin.castAdd 13 ⟨v.val, h13⟩ = v from Fin.ext rfl],
            Fin.ext rfl⟩
        · right
          exact ⟨⟨v.val - 13, by omega⟩,
            by rwa [show Fin.natAdd 13 ⟨v.val - 13, by omega⟩ = v from Fin.ext (by simp; omega)],
            Fin.ext (by simp; omega)⟩
      · rintro (⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩) <;> assumption
    have hdisj : Disjoint (P.image (Fin.castAdd 13)) (L.image (Fin.natAdd 13)) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv1
      obtain ⟨l, _, h2⟩ := Finset.mem_image.mp hv2
      exact hcast_ne_nat p l h2.symm
    have hsum : P.card + L.card = 12 := by
      have h1 : K.card = (P.image (Fin.castAdd 13)).card + (L.image (Fin.natAdd 13)).card := by
        rw [hKeq, Finset.card_union_of_disjoint hdisj]
      rw [Finset.card_image_of_injective _ hcast_inj,
        Finset.card_image_of_injective _ hnat_inj] at h1
      omega
    have hmiss : ∀ p ∈ P, ∀ l ∈ L, p ∉ singerLines3 l := by
      intro p hp l hl hpl
      have hpK : Fin.castAdd 13 p ∈ K := (Finset.mem_filter.mp hp).2
      have hlK : Fin.natAdd 13 l ∈ K := (Finset.mem_filter.mp hl).2
      exact hindep _ hpK _ hlK ((hadj_cast_nat p l).mpr hpl)
    by_cases hP0 : P.card = 0
    · right
      intro v hv
      rw [hKeq, Finset.mem_union] at hv
      rcases hv with h1 | h2
      · rw [Finset.card_eq_zero.mp hP0] at h1; simp at h1
      · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp h2; simp
    · by_cases hL0 : L.card = 0
      · left
        intro v hv
        rw [hKeq, Finset.mem_union] at hv
        rcases hv with h1 | h2
        · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h1; exact p.isLt
        · rw [Finset.card_eq_zero.mp hL0] at h2; simp at h2
      · exfalso
        have hP_le : ∀ n : ℕ, (L.card = 1 → P.card ≤ 9) ∧ (L.card = 2 → P.card ≤ 6) ∧
            (3 ≤ L.card → P.card ≤ 4) := by
          intro _
          refine ⟨?_, ?_, ?_⟩
          · intro h1
            obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < L.card)
            have hsub : P ⊆ Finset.univ.filter fun p => p ∉ singerLines3 l := by
              intro p hp; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmiss p hp l hl⟩
            exact (Finset.card_le_card hsub).trans (le_of_eq (hmiss_l1 l))
          · intro h2
            obtain ⟨l1, hl1, l2, hl2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < L.card)
            have hsub : P ⊆ Finset.univ.filter fun p =>
                p ∉ singerLines3 l1 ∧ p ∉ singerLines3 l2 := by
              intro p hp
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmiss p hp l1 hl1, hmiss p hp l2 hl2⟩
            exact (Finset.card_le_card hsub).trans (le_of_eq (hmiss_l2 l1 l2 hne))
          · intro h3
            obtain ⟨l1, hl1, l2, hl2, l3, hl3, h12, h13, h23⟩ :=
              Finset.two_lt_card.mp (by omega : 2 < L.card)
            have hsub : P ⊆ Finset.univ.filter fun p =>
                p ∉ singerLines3 l1 ∧ p ∉ singerLines3 l2 ∧ p ∉ singerLines3 l3 := by
              intro p hp
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, hmiss p hp l1 hl1, hmiss p hp l2 hl2, hmiss p hp l3 hl3⟩
            exact (Finset.card_le_card hsub).trans (hmiss_l3 l1 l2 l3 h12 h13 h23)
        have hL_le : (P.card = 1 → L.card ≤ 9) ∧ (P.card = 2 → L.card ≤ 6) ∧
            (3 ≤ P.card → L.card ≤ 4) := by
          refine ⟨?_, ?_, ?_⟩
          · intro h1
            obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
            have hsub : L ⊆ Finset.univ.filter fun l => p ∉ singerLines3 l := by
              intro l hl; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmiss p hp l hl⟩
            exact (Finset.card_le_card hsub).trans (le_of_eq (hmiss_p1 p))
          · intro h2
            obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
            have hsub : L ⊆ Finset.univ.filter fun l =>
                p1 ∉ singerLines3 l ∧ p2 ∉ singerLines3 l := by
              intro l hl
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmiss p1 hp1 l hl, hmiss p2 hp2 l hl⟩
            exact (Finset.card_le_card hsub).trans (le_of_eq (hmiss_p2 p1 p2 hne))
          · intro h3
            obtain ⟨p1, hp1, p2, hp2, p3, hp3, h12, h13, h23⟩ :=
              Finset.two_lt_card.mp (by omega : 2 < P.card)
            have hsub : L ⊆ Finset.univ.filter fun l =>
                p1 ∉ singerLines3 l ∧ p2 ∉ singerLines3 l ∧ p3 ∉ singerLines3 l := by
              intro l hl
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, hmiss p1 hp1 l hl, hmiss p2 hp2 l hl, hmiss p3 hp3 l hl⟩
            exact (Finset.card_le_card hsub).trans (hmiss_p3 p1 p2 p3 h12 h13 h23)
        have hp' := hP_le 0
        omega
  have hCover4 : ∀ (U : Finset (Sym2 (Fin 26))) (K : Finset (Fin 26)),
      U ⊆ G3.edgeFinset → U.card = 4 →
      (G3.deleteEdges ↑U).IsVertexCover (K : Set (Fin 26)) → K.card ≤ 12 →
      ∃ w : Fin 26, ∀ v : Fin 26, G3.Adj w v → s(w, v) ∈ U := by
    intro U K hUsub hUcard hK hKle
    have hKb := hCoverBound U K hK
    have hKcard : K.card = 12 := by omega
    have hsub : G3.edgeFinset \ U ⊆ K.biUnion inc := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        have hadj : (G3.deleteEdges ↑U).Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨he.1, he.2⟩
        rcases hK hadj with ha | hb
        · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr
            ⟨SimpleGraph.mem_edgeFinset.mpr he.1, Sym2.mem_mk_left a b⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr
            ⟨SimpleGraph.mem_edgeFinset.mpr he.1, Sym2.mem_mk_right a b⟩⟩
    have hsdiff_card : (G3.edgeFinset \ U).card = 48 := by
      have := Finset.card_sdiff_add_card_eq_card hUsub
      omega
    have hsum : ∑ v ∈ K, (inc v).card = 48 := by
      simp only [hinc_card, Finset.sum_const, smul_eq_mul, hKcard]
    have hbi_le : (K.biUnion inc).card ≤ 48 := by
      calc (K.biUnion inc).card ≤ ∑ v ∈ K, (inc v).card := Finset.card_biUnion_le
        _ = 48 := hsum
    have hbi_eq : G3.edgeFinset \ U = K.biUnion inc :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hbi_card : (K.biUnion inc).card = ∑ v ∈ K, (inc v).card := by
      rw [← hbi_eq, hsdiff_card, hsum]
    have hindep : ∀ u ∈ K, ∀ v ∈ K, ¬ G3.Adj u v := by
      intro u hu v hv hadj
      have hne : u ≠ v := G3.ne_of_adj hadj
      have hv1 : v ∈ K.erase u := Finset.mem_erase.mpr ⟨hne.symm, hv⟩
      let K' := (K.erase u).erase v
      have hKsplit : K = insert u (insert v K') := by
        rw [Finset.insert_erase hv1, Finset.insert_erase hu]
      have hu_nmem : u ∉ insert v K' := by
        rw [Finset.insert_erase hv1]; exact Finset.notMem_erase u K
      have hv_nmem : v ∉ K' := Finset.notMem_erase v (K.erase u)
      have hsum_split : ∑ x ∈ K, (inc x).card = (inc u).card + (inc v).card + ∑ x ∈ K', (inc x).card := by
        conv_lhs => rw [hKsplit]
        rw [Finset.sum_insert hu_nmem, Finset.sum_insert hv_nmem]
        omega
      have hbi_split : K.biUnion inc = (inc u ∪ inc v) ∪ K'.biUnion inc := by
        conv_lhs => rw [hKsplit]
        rw [Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
      have h_inter_pos : 0 < (inc u ∩ inc v).card := Finset.card_pos.mpr
        ⟨s(u, v), Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hadj, Sym2.mem_mk_left u v⟩,
           Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hadj, Sym2.mem_mk_right u v⟩⟩⟩
      have h_uv_lt : (inc u ∪ inc v).card < (inc u).card + (inc v).card := by
        have := Finset.card_union_add_card_inter (inc u) (inc v)
        omega
      have h_card_le : (K.biUnion inc).card ≤ (inc u ∪ inc v).card + (K'.biUnion inc).card := by
        rw [hbi_split]; exact Finset.card_union_le _ _
      have h_rest_le : (K'.biUnion inc).card ≤ ∑ x ∈ K', (inc x).card := Finset.card_biUnion_le
      omega
    rcases hindep12 K hKcard hindep with hpts | hlns
    · let S : Finset (Fin 13) := Finset.univ.filter fun p => Fin.castAdd 13 p ∈ K
      have hScard : S.card = 12 := by
        have hKe : K = S.image (Fin.castAdd 13) := by
          ext v
          simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hv
            exact ⟨⟨v.val, hpts v hv⟩,
              by rwa [show Fin.castAdd 13 ⟨v.val, hpts v hv⟩ = v from Fin.ext rfl], Fin.ext rfl⟩
          · rintro ⟨p, hp, rfl⟩; exact hp
        rw [hKe, Finset.card_image_of_injective _ hcast_inj] at hKcard
        exact hKcard
      have hne_univ : S ≠ Finset.univ := by
        intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hScard; omega
      obtain ⟨p0, hp0⟩ : ∃ p0 : Fin 13, p0 ∉ S := by
        by_contra hall; push Not at hall
        exact hne_univ (Finset.eq_univ_of_forall hall)
      refine ⟨Fin.castAdd 13 p0, fun v hv => ?_⟩
      have hwK : Fin.castAdd 13 p0 ∉ K := fun h => hp0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hvK : v ∉ K := by
        intro h
        have h13 := hpts v h
        obtain ⟨p', l', _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hv
        · have hv2 := congrArg Fin.val h2; simp only [Fin.val_natAdd] at hv2; omega
        · exact hcast_ne_nat p0 l' h2
      by_contra hnotU
      have hmem : s(Fin.castAdd 13 p0, v) ∈ G3.edgeFinset \ U :=
        Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hv, hnotU⟩
      rw [hbi_eq, Finset.mem_biUnion] at hmem
      obtain ⟨z, hzK, hze⟩ := hmem
      have hzmem := (Finset.mem_filter.mp hze).2
      rw [Sym2.mem_iff] at hzmem
      rcases hzmem with rfl | rfl
      · exact hwK hzK
      · exact hvK hzK
    · let S : Finset (Fin 13) := Finset.univ.filter fun l => Fin.natAdd 13 l ∈ K
      have hScard : S.card = 12 := by
        have hKe : K = S.image (Fin.natAdd 13) := by
          ext v
          simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hv
            have h13 := hlns v hv
            exact ⟨⟨v.val - 13, by omega⟩,
              by rwa [show Fin.natAdd 13 ⟨v.val - 13, by omega⟩ = v from Fin.ext (by simp; omega)],
              Fin.ext (by simp; omega)⟩
          · rintro ⟨l, hl, rfl⟩; exact hl
        rw [hKe, Finset.card_image_of_injective _ hnat_inj] at hKcard
        exact hKcard
      have hne_univ : S ≠ Finset.univ := by
        intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hScard; omega
      obtain ⟨l0, hl0⟩ : ∃ l0 : Fin 13, l0 ∉ S := by
        by_contra hall; push Not at hall
        exact hne_univ (Finset.eq_univ_of_forall hall)
      refine ⟨Fin.natAdd 13 l0, fun v hv => ?_⟩
      have hwK : Fin.natAdd 13 l0 ∉ K := fun h => hl0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hvK : v ∉ K := by
        intro h
        have h13 := hlns v h
        obtain ⟨p', l', _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hv
        · exact hcast_ne_nat p' l0 h1.symm
        · have hv2 := congrArg Fin.val h1; simp only [Fin.val_castAdd] at hv2; omega
      by_contra hnotU
      have hmem : s(Fin.natAdd 13 l0, v) ∈ G3.edgeFinset \ U :=
        Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hv, hnotU⟩
      rw [hbi_eq, Finset.mem_biUnion] at hmem
      obtain ⟨z, hzK, hze⟩ := hmem
      have hzmem := (Finset.mem_filter.mp hze).2
      rw [Sym2.mem_iff] at hzmem
      rcases hzmem with rfl | rfl
      · exact hwK hzK
      · exact hvK hzK
  have hAO2_C : IsAO2 26 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact (hwf j _ (List.getElem?_eq_getElem hj)).1
    · intro j hj w hw
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      have hga : gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
        simp [List.getD_eq_getElem?_getD, hget]
      rw [hga] at hw
      obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hwf j _ hget
      rw [hinp] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨_, a, b, hinp, _⟩ := hwf j _ (List.getElem?_eq_getElem hj)
      rw [hinp]; rfl
  have hgraph_iff : ∀ x : Fin 26 → Bool,
      graphFun G3 ∅ x = true ↔
      ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := by
    intro x
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) ||
      decide (∃ u v, G3.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, ⟨u, t, hinc, hor⟩, ha, hb⟩
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨u, t, (hsinger_iff u t).mpr hinc, ha, hb⟩
      · exact ⟨u, t, (hsinger_iff u t).mpr hinc, hb, ha⟩
    · rintro ⟨u, t, hinc, hu, ht⟩
      exact ⟨Fin.castAdd 13 u, Fin.natAdd 13 t,
        ⟨u, t, (hsinger_iff u t).mp hinc, Or.inl ⟨rfl, rfl⟩⟩, hu, ht⟩
  have hfun_C : circuitFun 26 C = graphFun G3 ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    exact (heval x).trans (hgraph_iff x).symm
  have hex : ∃ k : ℕ, ∃ C0 : Circuit, IsAO2 26 C0 ∧ circuitFun 26 C0 = graphFun G3 ∅ ∧
      C0.size = k := ⟨C.size, C, hAO2_C, hfun_C, rfl⟩
  obtain ⟨C0, hC0_ao, hC0_fun, hC0_sz⟩ := Nat.find_spec hex
  have hC0_le : C0.size ≤ C.size := by
    rw [hC0_sz]
    exact Nat.find_min' hex ⟨C, hAO2_C, hfun_C, rfl⟩
  have hC0_least : IsLeastAO G3 C0 := by
    refine ⟨hC0_ao, hC0_fun, ?_⟩
    intro C' h1 h2
    rw [hC0_sz]
    exact Nat.find_min' hex ⟨C', h1, h2, rfl⟩
  obtain ⟨D, hD_least, hD_top, hD_sz_eq, hD_acc, hD_cov⟩ := hTop G3 C0 hG3 hC0_least
  have hD_sz : D.size ≤ 62 := by omega
  have hD_ao : IsAO2 26 D := hD_least.1
  have hD_fun : circuitFun 26 D = graphFun G3 ∅ := hD_least.2.1
  -- Basic circuit evaluation and OR-closure lemmas for D
  let step : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have hstep_len : ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g gs ih =>
      intro ws
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have hstep_lt : ∀ (gs : List Gate) (ws : List Bool) (i : ℕ),
      i < ws.length → (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      rw [List.foldl_cons]
      have hlt' : i < (step ws g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step ws g) i hlt']
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hstep_gate : ∀ (gs : List Gate) (ws : List Bool) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (gs.foldl step ws).getD (ws.length + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < ws.length + j then (gs.foldl step ws).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro ws j g hj; simp at hj
    | cons g0 gs ih =>
      intro ws j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt' : ws.length < (step ws g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        rw [hstep_lt gs (step ws g0) ws.length hlt']
        have hself : (step ws g0).getD ws.length false =
            g0.op.eval (g0.inputs.map fun i => ws.getD i false) := by
          simp only [step, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl ws.length)]
          simp
        rw [hself]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < ws.length
        · have hilt : i < (step ws g0).length := by
            simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          simp only [hi, ↓reduceIte]
          rw [hstep_lt gs (step ws g0) i hilt]
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · simp only [hi, ↓reduceIte]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
            Option.getD_none]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hlen1 : (step ws g0).length = ws.length + 1 := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
        have hidx : ws.length + (j + 1) = (step ws g0).length + j := by omega
        rw [hidx]
        exact ih (step ws g0) j g hj
  have hga_eq : ∀ (j : ℕ) (hj : j < D.gates.length), gateAt D j = D.gates[j]'hj := by
    intro j hj
    change D.gates.getD j ⟨GateOp.or, []⟩ = D.gates[j]'hj
    simp [List.getD_eq_getElem?_getD, hj]
  have hga_inputs : ∀ (j : ℕ) (hj : j < D.gates.length), (gateAt D j).inputs = [opnd D j 0, opnd D j 1] := by
    intro j hj
    have hlen2 : (gateAt D j).inputs.length = 2 := by
      rw [hga_eq j hj]
      exact hD_ao.2.2 (D.gates[j]'hj) (List.getElem_mem hj)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen2
    have h0 : opnd D j 0 = a := by change (gateAt D j).inputs.getD 0 0 = a; rw [hab]; rfl
    have h1 : opnd D j 1 = b := by change (gateAt D j).inputs.getD 1 0 = b; rw [hab]; rfl
    rw [h0, h1, hab]
  have hopnd_lt : ∀ j < D.gates.length, ∀ b : Fin 2, opnd D j b < 26 + j := by
    intro j hj b
    have hin := hga_inputs j hj
    have hmem : opnd D j b ∈ (gateAt D j).inputs := by
      rw [hin]; fin_cases b <;> simp
    exact hD_ao.2.1 j hj _ hmem
  have hwire_in : ∀ (x : Fin 26 → Bool) (u : ℕ) (hu : u < 26),
      wireVal 26 D u x = x ⟨u, hu⟩ := by
    intro x u hu
    change (D.gates.foldl step (List.ofFn x)).getD u false = x ⟨u, hu⟩
    have hlt' : u < (List.ofFn x).length := by simp [hu]
    rw [hstep_lt D.gates (List.ofFn x) u hlt', List.getD_eq_getElem _ _ hlt', List.getElem_ofFn]
  have hwire_ge : ∀ (x : Fin 26 → Bool) (u : ℕ), 26 + D.gates.length ≤ u →
      wireVal 26 D u x = false := by
    intro x u hu
    change (D.gates.foldl step (List.ofFn x)).getD u false = false
    rw [List.getD_eq_default]
    rw [hstep_len, List.length_ofFn]; omega
  have hwire_gate : ∀ (x : Fin 26 → Bool) (j : ℕ) (hj : j < D.gates.length),
      wireVal 26 D (26 + j) x =
        (gateAt D j).op.eval [wireVal 26 D (opnd D j 0) x, wireVal 26 D (opnd D j 1) x] := by
    intro x j hj
    change (D.gates.foldl step (List.ofFn x)).getD (26 + j) false = _
    have hget : D.gates[j]? = some (gateAt D j) := by
      rw [hga_eq j hj]; exact List.getElem?_eq_getElem hj
    have h1 := hstep_gate D.gates (List.ofFn x) j (gateAt D j) hget
    rw [List.length_ofFn] at h1
    rw [h1, hga_inputs j hj]
    have h0 := hopnd_lt j hj 0
    have h1' := hopnd_lt j hj 1
    simp only [List.map_cons, List.map_nil, h0, h1', ↓reduceIte]
    rfl
  have horStep_eq : ∀ (cs : List (List ℕ)) (g : Gate),
      orStep 26 cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
          (fun w => cs.getD (w - 26) [])
        else [])] := by
    intro cs g
    change cs ++ [cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq _ _) _ _)] = _
    by_cases h : g.op = GateOp.or <;> simp only [h, ↓reduceIte]
  have horStep_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, horStep_eq, List.length_append, List.length_cons, List.length_nil,
        List.length_cons]
      omega
  have horStep_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ),
      i < cs.length → (gs.foldl (orStep 26) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      rw [List.foldl_cons]
      have hlt' : i < (orStep 26 cs g).length := by
        rw [horStep_eq, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (orStep 26 cs g) i hlt', horStep_eq]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have horStep_gate : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (gs.foldl (orStep 26) cs).getD (cs.length + j) [] =
        (cs.length + j) :: (if g.op = GateOp.or then
          (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + (cs.length + j)))).flatMap
            (fun w => (gs.foldl (orStep 26) cs).getD (w - 26) [])
          else []) := by
    intro gs
    induction gs with
    | nil => intro cs j g hj; simp at hj
    | cons g0 gs ih =>
      intro cs j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt' : cs.length < (orStep 26 cs g0).length := by
          rw [horStep_eq, List.length_append, List.length_cons, List.length_nil]; omega
        rw [horStep_lt gs (orStep 26 cs g0) cs.length hlt']
        have hself : (orStep 26 cs g0).getD cs.length [] =
            cs.length :: (if g0.op = GateOp.or then
              (g0.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
                (fun w => cs.getD (w - 26) [])
              else []) := by
          rw [horStep_eq]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl cs.length)]
          simp
        rw [hself]
        congr 1
        split_ifs
        · apply List.flatMap_congr
          intro w hw
          simp only [List.mem_filter, decide_eq_true_eq] at hw
          have hwlt : w - 26 < cs.length := by omega
          have hwlt1 : w - 26 < (orStep 26 cs g0).length := by
            rw [horStep_eq, List.length_append, List.length_cons, List.length_nil]; omega
          rw [horStep_lt gs (orStep 26 cs g0) (w - 26) hwlt1, horStep_eq]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
        · rfl
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hlen1 : (orStep 26 cs g0).length = cs.length + 1 := by
          rw [horStep_eq, List.length_append, List.length_cons, List.length_nil]
        have hidx : cs.length + (j + 1) = (orStep 26 cs g0).length + j := by omega
        rw [hidx]
        exact ih (orStep 26 cs g0) j g hj
  have hOrReaches_def : ∀ (w g : ℕ), OrReaches 26 D w g ↔
      26 ≤ w ∧ g ∈ (D.gates.foldl (orStep 26) []).getD (w - 26) [] := fun _ _ => Iff.rfl
  have hOrReaches_iff : ∀ (w g : ℕ), OrReaches 26 D w g ↔
      26 ≤ w ∧ w - 26 < D.gates.length ∧
        (g = w - 26 ∨ ((gateAt D (w - 26)).op = GateOp.or ∧
          ∃ b : Fin 2, OrReaches 26 D (opnd D (w - 26) b) g)) := by
    intro w g
    rw [hOrReaches_def]
    by_cases h26 : 26 ≤ w
    · by_cases hlt' : w - 26 < D.gates.length
      · have hget : D.gates[w - 26]? = some (gateAt D (w - 26)) := by
          rw [hga_eq _ hlt']; exact List.getElem?_eq_getElem hlt'
        have h1 := horStep_gate D.gates [] (w - 26) (gateAt D (w - 26)) hget
        simp only [List.length_nil, Nat.zero_add] at h1
        rw [h1]
        simp only [h26, hlt', true_and, List.mem_cons]
        constructor
        · rintro (rfl | hmem)
          · exact Or.inl rfl
          · right
            split_ifs at hmem with hop
            · rw [List.mem_flatMap] at hmem
              obtain ⟨u, hu, hgu⟩ := hmem
              simp only [List.mem_filter, decide_eq_true_eq] at hu
              rw [hga_inputs _ hlt'] at hu
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu.1 with rfl | rfl
              · exact ⟨hop, 0, (hOrReaches_def _ _).mpr ⟨hu.2.1, hgu⟩⟩
              · exact ⟨hop, 1, (hOrReaches_def _ _).mpr ⟨hu.2.1, hgu⟩⟩
            · simp at hmem
        · rintro (rfl | ⟨hop, b, hbg⟩)
          · exact Or.inl rfl
          · right
            obtain ⟨hb26, hbg'⟩ := (hOrReaches_def _ _).mp hbg
            simp only [hop, ↓reduceIte, List.mem_flatMap]
            refine ⟨opnd D (w - 26) b, ?_, hbg'⟩
            simp only [List.mem_filter, decide_eq_true_eq]
            refine ⟨?_, hb26, hopnd_lt _ hlt' b⟩
            rw [hga_inputs _ hlt']; fin_cases b <;> simp
      · have hge : (D.gates.foldl (orStep 26) []).length ≤ w - 26 := by
          rw [horStep_len, List.length_nil, Nat.zero_add]; omega
        rw [List.getD_eq_default _ _ hge]
        simp [h26, hlt']
    · simp [h26]
  have hOrReaches_self : ∀ k < D.gates.length, OrReaches 26 D (26 + k) k := by
    intro k hk
    rw [hOrReaches_iff]
    exact ⟨by omega, by omega, Or.inl (by omega)⟩
  have hOrReaches_lt : ∀ w g, OrReaches 26 D w g → g < D.gates.length ∧ 26 + g ≤ w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro g h
      obtain ⟨h26, hlt', rfl | ⟨_, b, hb⟩⟩ := (hOrReaches_iff w g).mp h
      · exact ⟨hlt', by omega⟩
      · have hblt := hopnd_lt (w - 26) hlt' b
        obtain ⟨hglt, hg26⟩ := ih (opnd D (w - 26) b) (by omega) g hb
        exact ⟨hglt, by omega⟩
  have hOrReaches_trans : ∀ w k g, OrReaches 26 D w k → OrReaches 26 D (26 + k) g →
      OrReaches 26 D w g := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro k g hwk hkg
      obtain ⟨h26, hlt', hcase⟩ := (hOrReaches_iff w k).mp hwk
      rcases hcase with rfl | ⟨hop, b, hb⟩
      · have heq : 26 + (w - 26) = w := by omega
        rwa [heq] at hkg
      · rw [hOrReaches_iff]
        refine ⟨h26, hlt', Or.inr ⟨hop, b, ?_⟩⟩
        have hblt := hopnd_lt (w - 26) hlt' b
        exact ih (opnd D (w - 26) b) (by omega) k g hb hkg
  have hEval_or : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) :=
    fun a b => by cases a <;> cases b <;> rfl
  have hEval_and : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) :=
    fun a b => by cases a <;> cases b <;> rfl
  have hOrReaches_up : ∀ w g (x : Fin 26 → Bool), OrReaches 26 D w g →
      gateVal 26 D g x = true → wireVal 26 D w x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro g x hwg hgx
      obtain ⟨h26, hlt', hcase⟩ := (hOrReaches_iff w g).mp hwg
      rcases hcase with rfl | ⟨hop, b, hb⟩
      · have heq : 26 + (w - 26) = w := by omega
        rw [← heq]; exact hgx
      · have hblt := hopnd_lt (w - 26) hlt' b
        have hbv := ih (opnd D (w - 26) b) (by omega) g x hb hgx
        have heq : 26 + (w - 26) = w := by omega
        rw [← heq, hwire_gate x (w - 26) hlt', hop, hEval_or]
        fin_cases b
        · change wireVal 26 D (opnd D (w - 26) 0) x = true at hbv
          rw [hbv]; rfl
        · change wireVal 26 D (opnd D (w - 26) 1) x = true at hbv
          rw [hbv]; exact Bool.or_true _
  -- Cone characterization
  have hconeStep_eq : ∀ (cs : List (List ℕ)) (g : Gate),
      coneStep 26 cs g = cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
        (fun w => (w - 26) :: cs.getD (w - 26) [])] := fun _ _ => rfl
  have hcone_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, hconeStep_eq, List.length_append, List.length_cons, List.length_nil,
        List.length_cons]
      omega
  have hcone_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ),
      i < cs.length → (gs.foldl (coneStep 26) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      rw [List.foldl_cons]
      have hlt' : i < (coneStep 26 cs g).length := by
        rw [hconeStep_eq, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (coneStep 26 cs g) i hlt', hconeStep_eq]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hcone_gate : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (gs.foldl (coneStep 26) cs).getD (cs.length + j) [] =
        (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + (cs.length + j)))).flatMap
          (fun w => (w - 26) :: (gs.foldl (coneStep 26) cs).getD (w - 26) []) := by
    intro gs
    induction gs with
    | nil => intro cs j g hj; simp at hj
    | cons g0 gs ih =>
      intro cs j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt' : cs.length < (coneStep 26 cs g0).length := by
          rw [hconeStep_eq, List.length_append, List.length_cons, List.length_nil]; omega
        rw [hcone_lt gs (coneStep 26 cs g0) cs.length hlt']
        have hself : (coneStep 26 cs g0).getD cs.length [] =
            (g0.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
              (fun w => (w - 26) :: cs.getD (w - 26) []) := by
          rw [hconeStep_eq]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl cs.length)]
          simp
        rw [hself]
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwlt : w - 26 < cs.length := by omega
        have hwlt1 : w - 26 < (coneStep 26 cs g0).length := by
          rw [hconeStep_eq, List.length_append, List.length_cons, List.length_nil]; omega
        rw [hcone_lt gs (coneStep 26 cs g0) (w - 26) hwlt1, hconeStep_eq]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hlen1 : (coneStep 26 cs g0).length = cs.length + 1 := by
          rw [hconeStep_eq, List.length_append, List.length_cons, List.length_nil]
        have hidx : cs.length + (j + 1) = (coneStep 26 cs g0).length + j := by omega
        rw [hidx]
        exact ih (coneStep 26 cs g0) j g hj
  have hInCone_step : ∀ (j : ℕ) (hj : j < D.gates.length) (b : Fin 2) (k : ℕ),
      26 ≤ opnd D j b → (k = opnd D j b - 26 ∨ InCone 26 D k (opnd D j b - 26)) →
      InCone 26 D k j := by
    intro j hj b k h26 hk
    change k ∈ (D.gates.foldl (coneStep 26) []).getD j []
    have hget : D.gates[j]? = some (gateAt D j) := by
      rw [hga_eq j hj]; exact List.getElem?_eq_getElem hj
    have hc := hcone_gate D.gates [] j (gateAt D j) hget
    simp only [List.length_nil, Nat.zero_add] at hc
    rw [hc, List.mem_flatMap]
    refine ⟨opnd D j b, ?_, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]
      refine ⟨?_, h26, hopnd_lt j hj b⟩
      rw [hga_inputs j hj]; fin_cases b <;> simp
    · rcases hk with rfl | hk
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hk
  have hOrReaches_cone : ∀ w h, OrReaches 26 D w h →
      h = w - 26 ∨ (26 ≤ w ∧ InCone 26 D h (w - 26)) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro h hwh
      obtain ⟨h26, hlt', rfl | ⟨_, b, hb⟩⟩ := (hOrReaches_iff w h).mp hwh
      · exact Or.inl rfl
      · right
        have hblt := hopnd_lt (w - 26) hlt' b
        have hb26 : 26 ≤ opnd D (w - 26) b := ((hOrReaches_iff _ _).mp hb).1
        exact ⟨h26, hInCone_step (w - 26) hlt' b h hb26
          (by rcases ih (opnd D (w - 26) b) (by omega) h hb with h1 | ⟨_, h2⟩
              · exact Or.inl h1
              · exact Or.inr h2)⟩
  have hOrReaches_inCone : ∀ a < D.gates.length, ∀ (b : Fin 2) (h : ℕ),
      OrReaches 26 D (opnd D a b) h → InCone 26 D h a := by
    intro a ha b h hrh
    have h26 : 26 ≤ opnd D a b := ((hOrReaches_iff _ _).mp hrh).1
    rcases hOrReaches_cone (opnd D a b) h hrh with h1 | ⟨_, h2⟩
    · exact hInCone_step a ha b h h26 (Or.inl h1)
    · exact hInCone_step a ha b h h26 (Or.inr h2)
  -- orIn properties
  have hpair_eq : ∀ u v w : Fin 26, pairInput u v w = decide (w = u ∨ w = v) := fun _ _ _ => rfl
  have hpair_left : ∀ u v : Fin 26, pairInput u v u = true := fun u v => by
    rw [hpair_eq, decide_eq_true_eq]; exact Or.inl rfl
  have hpair_right : ∀ u v : Fin 26, pairInput u v v = true := fun u v => by
    rw [hpair_eq, decide_eq_true_eq]; exact Or.inr rfl
  have horIn_mem : ∀ (w : ℕ) (i : Fin 26), i ∈ orIn 26 D w ↔
      i.val = w ∨ ∃ k < D.gates.length, OrReaches 26 D w k ∧ (gateAt D k).op = GateOp.or ∧
        i.val ∈ (gateAt D k).inputs := by
    intro w i
    change i ∈ Finset.univ.filter _ ↔ _
    rw [Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ i)
  have horIn_val : ∀ (w : ℕ) (i : Fin 26) (x : Fin 26 → Bool),
      i ∈ orIn 26 D w → x i = true → wireVal 26 D w x = true := by
    intro w i x hi hxi
    rw [horIn_mem] at hi
    rcases hi with rfl | ⟨k, hk, hwk, hop, hmem⟩
    · rw [hwire_in x i.val i.isLt]; exact hxi
    · apply hOrReaches_up w k x hwk
      show wireVal 26 D (26 + k) x = true
      rw [hwire_gate x k hk, hop, hEval_or]
      rw [hga_inputs k hk, List.mem_cons, List.mem_singleton] at hmem
      rcases hmem with h0 | h1
      · rw [← h0, hwire_in x i.val i.isLt, hxi]; rfl
      · rw [← h1, hwire_in x i.val i.isLt, hxi]; exact Bool.or_true _
  have horIn_sub : ∀ (w k : ℕ), OrReaches 26 D w k → orIn 26 D (26 + k) ⊆ orIn 26 D w := by
    intro w k hwk i hi
    rw [horIn_mem] at hi ⊢
    rcases hi with h1 | ⟨m, hm, hkm, hop, hmem⟩
    · have := i.isLt; omega
    · exact Or.inr ⟨m, hm, hOrReaches_trans w k m hwk hkm, hop, hmem⟩
  have horIn_and_empty : ∀ h, (gateAt D h).op = GateOp.and → orIn 26 D (26 + h) = ∅ := by
    intro h hop
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [horIn_mem] at hi
    rcases hi with h1 | ⟨k, hk, hhk, hkop, _⟩
    · have := i.isLt; omega
    · obtain ⟨_, _, hcase⟩ := (hOrReaches_iff (26 + h) k).mp hhk
      simp only [Nat.add_sub_cancel_left] at hcase
      rcases hcase with rfl | ⟨hor, _⟩
      · rw [hop] at hkop; cases hkop
      · rw [hop] at hor; cases hor
  have horIn_or_union : ∀ k < D.gates.length, (gateAt D k).op = GateOp.or →
      orIn 26 D (26 + k) = orIn 26 D (opnd D k 0) ∪ orIn 26 D (opnd D k 1) := by
    intro k hk hop
    ext i
    rw [Finset.mem_union, horIn_mem, horIn_mem, horIn_mem]
    constructor
    · rintro (h1 | ⟨m, hm, hkm, hmop, hmem⟩)
      · have := i.isLt; omega
      · obtain ⟨_, _, hcase⟩ := (hOrReaches_iff (26 + k) m).mp hkm
        simp only [Nat.add_sub_cancel_left] at hcase
        rcases hcase with hmk | ⟨_, b, hb⟩
        · rw [hmk] at hmem
          rw [hga_inputs k hk, List.mem_cons, List.mem_singleton] at hmem
          rcases hmem with h0 | h1
          · exact Or.inl (Or.inl h0)
          · exact Or.inr (Or.inl h1)
        · fin_cases b
          · exact Or.inl (Or.inr ⟨m, hm, hb, hmop, hmem⟩)
          · exact Or.inr (Or.inr ⟨m, hm, hb, hmop, hmem⟩)
    · rintro ((h0 | ⟨m, hm, h0, hmop, hmem⟩) | (h1 | ⟨m, hm, h1, hmop, hmem⟩))
      · refine Or.inr ⟨k, hk, hOrReaches_self k hk, hop, ?_⟩
        rw [hga_inputs k hk]; simp [h0]
      · refine Or.inr ⟨m, hm, ?_, hmop, hmem⟩
        rw [hOrReaches_iff]; simp only [Nat.add_sub_cancel_left]
        exact ⟨by omega, hk, Or.inr ⟨hop, 0, h0⟩⟩
      · refine Or.inr ⟨k, hk, hOrReaches_self k hk, hop, ?_⟩
        rw [hga_inputs k hk]; simp [h1]
      · refine Or.inr ⟨m, hm, ?_, hmop, hmem⟩
        rw [hOrReaches_iff]; simp only [Nat.add_sub_cancel_left]
        exact ⟨by omega, hk, Or.inr ⟨hop, 1, h1⟩⟩
  have hgraph_unit : ∀ u : Fin 26, graphFun G3 ∅ (pairInput u u) = false := by
    intro u
    rw [Bool.eq_false_iff]
    intro h
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), pairInput u u a = true) ||
      decide (∃ a b, G3.Adj a b ∧ pairInput u u a = true ∧ pairInput u u b = true)) = true at h
    rw [decide_eq_false (by rintro ⟨w, hw, _⟩; exact Finset.notMem_empty w hw), Bool.false_or,
      decide_eq_true_eq] at h
    obtain ⟨a, b, hab, ha, hb⟩ := h
    rw [hpair_eq, decide_eq_true_eq] at ha hb
    have ha' : a = u := ha.elim id id
    have hb' : b = u := hb.elim id id
    subst ha'; subst hb'
    exact G3.ne_of_adj hab rfl
  have hgraph_pair : ∀ u v : Fin 26, G3.Adj u v → graphFun G3 ∅ (pairInput u v) = true := by
    intro u v huv
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), pairInput u v a = true) ||
      decide (∃ a b, G3.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true)) = true
    rw [decide_eq_false (by rintro ⟨w, hw, _⟩; exact Finset.notMem_empty w hw), Bool.false_or,
      decide_eq_true_eq]
    exact ⟨u, v, huv, hpair_left u v, hpair_right u v⟩
  -- Downward trace through OR gates
  have htrace : ∀ (w : ℕ) (x : Fin 26 → Bool), wireVal 26 D w x = true →
      (∃ i ∈ orIn 26 D w, x i = true) ∨
      (∃ h < D.gates.length, (gateAt D h).op = GateOp.and ∧ OrReaches 26 D w h ∧
        gateVal 26 D h x = true) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x hw
      by_cases h26 : w < 26
      · left
        refine ⟨⟨w, h26⟩, ?_, ?_⟩
        · rw [horIn_mem]; exact Or.inl rfl
        · rwa [hwire_in x w h26] at hw
      · by_cases hlt' : w - 26 < D.gates.length
        · have heq : 26 + (w - 26) = w := by omega
          rcases hD_ao.1 D.gates[w - 26] (List.getElem_mem hlt') with hand | hor
          · right
            refine ⟨w - 26, hlt', ?_, ?_, ?_⟩
            · rw [hga_eq _ hlt']; exact hand
            · have hs := hOrReaches_self (w - 26) hlt'; rwa [heq] at hs
            · show wireVal 26 D (26 + (w - 26)) x = true; rw [heq]; exact hw
          · have hkop : (gateAt D (w - 26)).op = GateOp.or := by rw [hga_eq _ hlt']; exact hor
            rw [← heq, hwire_gate x (w - 26) hlt', hkop, hEval_or, Bool.or_eq_true] at hw
            have h0lt := hopnd_lt (w - 26) hlt' 0
            have h1lt := hopnd_lt (w - 26) hlt' 1
            rcases hw with h0 | h1
            · rcases ih (opnd D (w - 26) 0) (by omega) x h0 with ⟨i, hi, hxi⟩ | ⟨h, hh, hhop, hrh, hhv⟩
              · left
                refine ⟨i, ?_, hxi⟩
                rw [← heq, horIn_or_union _ hlt' hkop]
                exact Finset.mem_union_left _ hi
              · right
                refine ⟨h, hh, hhop, ?_, hhv⟩
                rw [hOrReaches_iff]
                exact ⟨by omega, hlt', Or.inr ⟨hkop, 0, hrh⟩⟩
            · rcases ih (opnd D (w - 26) 1) (by omega) x h1 with ⟨i, hi, hxi⟩ | ⟨h, hh, hhop, hrh, hhv⟩
              · left
                refine ⟨i, ?_, hxi⟩
                rw [← heq, horIn_or_union _ hlt' hkop]
                exact Finset.mem_union_right _ hi
              · right
                refine ⟨h, hh, hhop, ?_, hhv⟩
                rw [hOrReaches_iff]
                exact ⟨by omega, hlt', Or.inr ⟨hkop, 1, hrh⟩⟩
        · have hf := hwire_ge x w (by omega)
          rw [hw] at hf; cases hf
  have htops_mem : ∀ a : ℕ, a ∈ tops G3 D ↔
      a < D.gates.length ∧ (gateAt D a).op = GateOp.and ∧ BelowF G3 D a := by
    intro a
    change a ∈ (Finset.range D.gates.length).filter _ ↔ _
    rw [Finset.mem_filter, Finset.mem_range]
  have hjunk_mem : ∀ h : ℕ, h ∈ junk G3 D ↔
      h < D.gates.length ∧ (gateAt D h).op = GateOp.and ∧ h < D.gates.length ∧
        ∃ x : Fin 26 → Bool, gateVal 26 D h x = true ∧ graphFun G3 ∅ x = false := by
    intro h
    change h ∈ (Finset.range D.gates.length).filter _ ↔ _
    rw [Finset.mem_filter, Finset.mem_range]
    rfl
  have horN_mem : ∀ m : ℕ, m ∈ orN G3 D ↔
      m < D.gates.length ∧ (gateAt D m).op = GateOp.or ∧ ¬ BelowF G3 D m := by
    intro m
    change m ∈ (Finset.range D.gates.length).filter _ ↔ _
    rw [Finset.mem_filter, Finset.mem_range]
  have hlam_sides : ∀ m : ℕ, m ∈ lam G3 D →
      (orIn 26 D (opnd D m 0)).Nonempty ∧ (orIn 26 D (opnd D m 1)).Nonempty := by
    intro m hm
    change m ∈ (orN G3 D).filter _ at hm
    have h2 := (Finset.mem_filter.mp hm).2
    exact ⟨h2.1, h2.2.1⟩
  have hcentreless_mem : ∀ a : ℕ, a ∈ centreless G3 D ↔
      a ∈ tops G3 D ∧ (side (n := 26) D a 0 = ∅ ∨ side (n := 26) D a 1 = ∅) := by
    intro a
    change a ∈ (tops G3 D).filter _ ↔ _
    rw [Finset.mem_filter]
  have hstar_mk : ∀ a ∈ tops G3 D, ∀ u ∈ side (n := 26) D a 0, ∀ v ∈ side (n := 26) D a 1,
      s(u, v) ∈ starEdges G3 D := by
    intro a ha u hu v hv
    change s(u, v) ∈ (tops G3 D).biUnion _
    rw [Finset.mem_biUnion]
    refine ⟨a, ha, ?_⟩
    rw [Finset.mem_image]
    exact ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩
  -- Top side adjacency (for any top a, side a 0 and side a 1 are adjacent and disjoint)
  have hside_adj : ∀ a ∈ tops G3 D, ∀ u ∈ side (n := 26) D a 0, ∀ v ∈ side (n := 26) D a 1,
      G3.Adj u v := by
    intro a ha u hu v hv
    rw [htops_mem] at ha
    obtain ⟨halen, haop, habel⟩ := ha
    have hval : gateVal 26 D a (pairInput u v) = true := by
      show wireVal 26 D (26 + a) (pairInput u v) = true
      rw [hwire_gate (pairInput u v) a halen, haop, hEval_and]
      have h0 := horIn_val (opnd D a 0) u (pairInput u v) hu (hpair_left u v)
      have h1 := horIn_val (opnd D a 1) v (pairInput u v) hv (hpair_right u v)
      rw [h0, h1]; rfl
    have hF := habel (pairInput u v) hval
    change (decide (∃ w ∈ (∅ : Finset (Fin 26)), pairInput u v w = true) ||
      decide (∃ p q, G3.Adj p q ∧ pairInput u v p = true ∧ pairInput u v q = true)) = true at hF
    rw [decide_eq_false (by rintro ⟨w, hw, _⟩; exact Finset.notMem_empty w hw), Bool.false_or,
      decide_eq_true_eq] at hF
    obtain ⟨p, q, hpq, hp, hq⟩ := hF
    rw [hpair_eq, decide_eq_true_eq] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact (G3.ne_of_adj hpq rfl).elim
    · exact hpq
    · exact hpq.symm
    · exact (G3.ne_of_adj hpq rfl).elim
  -- Off-star tracing lemma
  have hoff_star : ∀ u v : Fin 26, s(u, v) ∈ Ustar G3 D →
      ∃ a ∈ tops G3 D,
        ((∃ b : Fin 2, (∃ i ∈ side (n := 26) D a b, i = u ∨ i = v) ∧
            ∃ h ∈ junk G3 D, OrReaches 26 D (opnd D a (1 - b)) h) ∨
         ((∃ h0 ∈ junk G3 D, OrReaches 26 D (opnd D a 0) h0) ∧
          (∃ h1 ∈ junk G3 D, OrReaches 26 D (opnd D a 1) h1))) := by
    intro u v huv
    change s(u, v) ∈ G3.edgeFinset \ starEdges G3 D at huv
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
    obtain ⟨hadj, hnotstar⟩ := huv
    have hout : wireVal 26 D D.output (pairInput u v) = true := by
      show circuitFun 26 D (pairInput u v) = true
      rw [hD_fun]; exact hgraph_pair u v hadj
    obtain ⟨a, halen, haop, haor, haval⟩ : ∃ a < D.gates.length, (gateAt D a).op = GateOp.and ∧
        OrReaches 26 D D.output a ∧ gateVal 26 D a (pairInput u v) = true := by
      rcases htrace D.output (pairInput u v) hout with ⟨i, hi, _⟩ | h
      · exfalso
        have h1 : wireVal 26 D D.output (pairInput i i) = true :=
          horIn_val D.output i (pairInput i i) hi (hpair_left i i)
        have h2 : circuitFun 26 D (pairInput i i) = true := h1
        rw [hD_fun, hgraph_unit i] at h2
        cases h2
      · exact h
    have habel : BelowF G3 D a := by
      intro x hx
      rw [← hD_fun]
      exact hOrReaches_up D.output a x haor hx
    have hatop : a ∈ tops G3 D := (htops_mem a).mpr ⟨halen, haop, habel⟩
    have hvals : wireVal 26 D (opnd D a 0) (pairInput u v) = true ∧
        wireVal 26 D (opnd D a 1) (pairInput u v) = true := by
      have h1 : wireVal 26 D (26 + a) (pairInput u v) = true := haval
      rw [hwire_gate (pairInput u v) a halen, haop, hEval_and, Bool.and_eq_true] at h1
      exact h1
    have hjunk_of : ∀ (b : Fin 2) (h : ℕ), h < D.gates.length → (gateAt D h).op = GateOp.and →
        OrReaches 26 D (opnd D a b) h → h ∈ junk G3 D := by
      intro b h hh hhop hrh
      have hcone := hOrReaches_inCone a halen b h hrh
      have hnb : ¬ BelowF G3 D h := fun hbh => hD_top h hh a halen hhop hbh haop hcone
      change ¬ (∀ x : Fin 26 → Bool, gateVal 26 D h x = true → graphFun G3 ∅ x = true) at hnb
      rw [Classical.not_forall] at hnb
      obtain ⟨x, hx⟩ := hnb
      rw [Classical.not_imp] at hx
      obtain ⟨hx1, hx2⟩ := hx
      exact (hjunk_mem h).mpr ⟨hh, hhop, hh, x, hx1, Bool.eq_false_iff.mpr hx2⟩
    refine ⟨a, hatop, ?_⟩
    rcases htrace (opnd D a 0) (pairInput u v) hvals.1 with ⟨i0, hi0, hxi0⟩ | ⟨h0, hh0, hop0, hr0, _⟩
    · rcases htrace (opnd D a 1) (pairInput u v) hvals.2 with ⟨i1, hi1, hxi1⟩ | ⟨h1, hh1, hop1, hr1, _⟩
      · exfalso
        have hne : i0 ≠ i1 := G3.ne_of_adj (hside_adj a hatop i0 hi0 i1 hi1)
        rw [hpair_eq, decide_eq_true_eq] at hxi0 hxi1
        have hseq : s(u, v) = s(i0, i1) := by
          rcases hxi0 with rfl | rfl <;> rcases hxi1 with rfl | rfl
          · exact (hne rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hne rfl).elim
        apply hnotstar
        rw [hseq]
        exact hstar_mk a hatop i0 hi0 i1 hi1
      · left
        rw [hpair_eq, decide_eq_true_eq] at hxi0
        refine ⟨0, ⟨i0, hi0, hxi0⟩, h1, hjunk_of 1 h1 hh1 hop1 hr1, hr1⟩
    · rcases htrace (opnd D a 1) (pairInput u v) hvals.2 with ⟨i1, hi1, hxi1⟩ | ⟨h1, hh1, hop1, hr1, _⟩
      · left
        rw [hpair_eq, decide_eq_true_eq] at hxi1
        refine ⟨1, ⟨i1, hi1, hxi1⟩, h0, hjunk_of 0 h0 hh0 hop0 hr0, hr0⟩
      · right
        exact ⟨⟨h0, hjunk_of 0 h0 hh0 hop0 hr0, hr0⟩, ⟨h1, hjunk_of 1 h1 hh1 hop1 hr1, hr1⟩⟩
  -- Finding a mixing gate in orN \ lam when an operand with nonempty orIn reaches a junk gate
  have hfind_mix : ∀ (w h : ℕ), h ∈ junk G3 D → OrReaches 26 D w h →
      (orIn 26 D w).Nonempty →
      ∃ m ∈ orN G3 D \ lam G3 D, OrReaches 26 D w m ∧ (orIn 26 D (26 + m)).Nonempty := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro h hh hwh hne
      have hhop : (gateAt D h).op = GateOp.and := ((hjunk_mem h).mp hh).2.1
      obtain ⟨h26, hlt', hcase⟩ := (hOrReaches_iff w h).mp hwh
      have heq : 26 + (w - 26) = w := by omega
      rcases hcase with rfl | ⟨hop, b, hb⟩
      · exfalso
        rw [← heq, horIn_and_empty _ hhop] at hne
        exact hne.ne_empty rfl
      · by_cases hbne : (orIn 26 D (opnd D (w - 26) b)).Nonempty
        · have hblt := hopnd_lt (w - 26) hlt' b
          obtain ⟨m, hm, hrm, hmne⟩ := ih (opnd D (w - 26) b) (by omega) h hh hb hbne
          refine ⟨m, hm, ?_, hmne⟩
          rw [hOrReaches_iff]
          exact ⟨h26, hlt', Or.inr ⟨hop, b, hrm⟩⟩
        · have hbemp : orIn 26 D (opnd D (w - 26) b) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hbne
          refine ⟨w - 26, ?_, ?_, by rw [heq]; exact hne⟩
          · rw [Finset.mem_sdiff]
            refine ⟨?_, ?_⟩
            · rw [horN_mem]
              refine ⟨hlt', hop, fun hbel => ?_⟩
              obtain ⟨i, hi⟩ := hne
              have hv : gateVal 26 D (w - 26) (pairInput i i) = true := by
                show wireVal 26 D (26 + (w - 26)) (pairInput i i) = true
                rw [heq]
                exact horIn_val w i (pairInput i i) hi (hpair_left i i)
              have hF := hbel (pairInput i i) hv
              rw [hgraph_unit i] at hF; cases hF
            · intro hlam
              have hl := hlam_sides _ hlam
              fin_cases b
              · exact hl.1.ne_empty hbemp
              · exact hl.2.ne_empty hbemp
          · have hs := hOrReaches_self (w - 26) hlt'; rwa [heq] at hs
  -- Choose a minimum vertex cover K of G3 \ Ustar
  let H := G3.deleteEdges (↑(Ustar G3 D) : Set (Sym2 (Fin 26)))
  let covers : Finset (Finset (Fin 26)) :=
    Finset.univ.filter fun K : Finset (Fin 26) => H.IsVertexCover (K : Set (Fin 26))
  have hcov_ne : covers.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun {u v} _ =>
      Or.inl (Finset.mem_univ u)⟩⟩
  obtain ⟨K, hKmem, hKmin⟩ := Finset.exists_min_image covers Finset.card hcov_ne
  have hK_ismin : IsMinCover H K :=
    ⟨(Finset.mem_filter.mp hKmem).2, fun A hA =>
      hKmin A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)⟩
  have hK_le_T : K.card ≤ (tops G3 D \ centreless G3 D).card := hD_cov K hK_ismin
  have hK_bound : 52 ≤ 4 * K.card + (Ustar G3 D).card := hCoverBound (Ustar G3 D) K hK_ismin.1
  have h5U : 8 + 8 * (centreless G3 D).card + 4 * (junk G3 D).card +
      4 * (orN G3 D \ lam G3 D).card ≤ 5 * (Ustar G3 D).card := by omega
  have hU_ne : (Ustar G3 D).Nonempty := Finset.card_pos.mp (by omega)
  have hJ_and_M : (junk G3 D).Nonempty ∧
      ((centreless G3 D).Nonempty ∨ (orN G3 D \ lam G3 D).Nonempty) := by
    obtain ⟨e, he⟩ := hU_ne
    revert he
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      obtain ⟨a, ha, hcase⟩ := hoff_star u v he
      rcases hcase with ⟨b, _, h, hh, hrh⟩ | ⟨⟨h0, hh0, hr0⟩, _⟩
      · refine ⟨⟨h, hh⟩, ?_⟩
        by_cases hside : (side (n := 26) D a (1 - b)).Nonempty
        · right
          obtain ⟨m, hm, _, _⟩ := hfind_mix (opnd D a (1 - b)) h hh hrh hside
          exact ⟨m, hm⟩
        · left
          refine ⟨a, ?_⟩
          rw [hcentreless_mem]
          have hemp := Finset.not_nonempty_iff_eq_empty.mp hside
          fin_cases b
          · exact ⟨ha, Or.inr hemp⟩
          · exact ⟨ha, Or.inl hemp⟩
      · refine ⟨⟨h0, hh0⟩, ?_⟩
        by_cases hside : (side (n := 26) D a 0).Nonempty
        · right
          obtain ⟨m, hm, _, _⟩ := hfind_mix (opnd D a 0) h0 hh0 hr0 hside
          exact ⟨m, hm⟩
        · left
          refine ⟨a, ?_⟩
          rw [hcentreless_mem]
          exact ⟨ha, Or.inl (Finset.not_nonempty_iff_eq_empty.mp hside)⟩
  have hJpos : 1 ≤ (junk G3 D).card := Finset.card_pos.mpr hJ_and_M.1
  have hCMpos : 1 ≤ (centreless G3 D).card ∨ 1 ≤ (orN G3 D \ lam G3 D).card := by
    rcases hJ_and_M.2 with h1 | h2
    · exact Or.inl (Finset.card_pos.mpr h1)
    · exact Or.inr (Finset.card_pos.mpr h2)
  by_cases hJ1 : (junk G3 D).card = 1
  · have hU4 : 4 ≤ (Ustar G3 D).card := by
      by_contra hU3
      have hK13 : 13 ≤ K.card := by omega
      omega
    exact hJunk1 G3 D hG3 hD_least hD_top hD_sz hJ1 hU4 h5U
  · have hJ2 : 2 ≤ (junk G3 D).card := by omega
    by_cases hC0 : centreless G3 D = ∅
    · have hCcard : (centreless G3 D).card = 0 := Finset.card_eq_zero.mpr hC0
      have hM1 : 1 ≤ (orN G3 D \ lam G3 D).card := by
        rcases hCMpos with h1 | h2
        · omega
        · exact h2
      have h5U' : 8 + 4 * (junk G3 D).card + 4 * (orN G3 D \ lam G3 D).card ≤
          5 * (Ustar G3 D).card := by omega
      have hU5 : 5 ≤ (Ustar G3 D).card := by
        by_contra hUle4
        have hUeq4 : (Ustar G3 D).card = 4 := by
          have : 4 ≤ (Ustar G3 D).card := by
            by_contra hU3
            have hK13 : 13 ≤ K.card := by omega
            omega
          omega
        have hKle12 : K.card ≤ 12 := by omega
        have hMle1 : (orN G3 D \ lam G3 D).card ≤ 1 := by omega
        obtain ⟨w, hw⟩ := hCover4 (Ustar G3 D) K Finset.sdiff_subset hUeq4 hK_ismin.1 hKle12
        -- Pick two distinct neighbors v1, v2 of w
        have hw4 := hinc_card w
        obtain ⟨e1, he1, e2, he2, he12⟩ := Finset.one_lt_card.mp (by omega : 1 < (inc w).card)
        have hget_nb : ∀ e ∈ inc w, ∃ v : Fin 26, G3.Adj w v ∧ e = s(w, v) := by
          intro e he
          induction e using Sym2.ind with
          | _ a b =>
            simp only [inc, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              Sym2.mem_iff] at he
            rcases he.2 with rfl | rfl
            · exact ⟨b, he.1, rfl⟩
            · exact ⟨a, he.1.symm, Sym2.eq_swap⟩
        obtain ⟨v1, hv1, rfl⟩ := hget_nb e1 he1
        obtain ⟨v2, hv2, rfl⟩ := hget_nb e2 he2
        have hv12 : v1 ≠ v2 := fun h => he12 (by rw [h])
        have hmix_of : ∀ v : Fin 26, G3.Adj w v →
            ∃ a ∈ tops G3 D, ∃ b : Fin 2, ∃ m ∈ orN G3 D \ lam G3 D,
              v ∈ side (n := 26) D a b ∧ OrReaches 26 D (opnd D a (1 - b)) m ∧
              (orIn 26 D (26 + m)).Nonempty := by
          intro v hv
          obtain ⟨a, ha, hcase⟩ := hoff_star w v (hw v hv)
          have ha_notc : a ∉ centreless G3 D := by rw [hC0]; exact Finset.notMem_empty a
          have hs0 : (side (n := 26) D a 0).Nonempty := by
            by_contra he0
            apply ha_notc
            rw [hcentreless_mem]
            exact ⟨ha, Or.inl (Finset.not_nonempty_iff_eq_empty.mp he0)⟩
          have hs1 : (side (n := 26) D a 1).Nonempty := by
            by_contra he1'
            apply ha_notc
            rw [hcentreless_mem]
            exact ⟨ha, Or.inr (Finset.not_nonempty_iff_eq_empty.mp he1')⟩
          rcases hcase with ⟨b, ⟨i, hi, hiwv⟩, h, hh, hrh⟩ | ⟨⟨h0, hh0, hr0⟩, ⟨h1, hh1, hr1⟩⟩
          · have hsb : (side (n := 26) D a (1 - b)).Nonempty := by
              fin_cases b
              · exact hs1
              · exact hs0
            rcases hiwv with hiw | hiv
            · exfalso
              rw [hiw] at hi
              obtain ⟨u', hu'⟩ := hsb
              have hadj' : G3.Adj w u' := by
                fin_cases b
                · exact hside_adj a ha w hi u' hu'
                · exact (hside_adj a ha u' hu' w hi).symm
              have hstar' : s(w, u') ∈ starEdges G3 D := by
                fin_cases b
                · exact hstar_mk a ha w hi u' hu'
                · rw [Sym2.eq_swap]; exact hstar_mk a ha u' hu' w hi
              exact (Finset.mem_sdiff.mp (hw u' hadj')).2 hstar'
            · rw [hiv] at hi
              obtain ⟨m, hm, hrm, hmne⟩ := hfind_mix (opnd D a (1 - b)) h hh hrh hsb
              exact ⟨a, ha, b, m, hm, hi, hrm, hmne⟩
          · exfalso
            obtain ⟨m0, hm0, hrm0, hm0ne⟩ := hfind_mix (opnd D a 0) h0 hh0 hr0 hs0
            obtain ⟨m1, hm1, hrm1, _⟩ := hfind_mix (opnd D a 1) h1 hh1 hr1 hs1
            have hm01 : m0 = m1 := Finset.card_le_one.mp hMle1 m0 hm0 m1 hm1
            subst hm01
            obtain ⟨z, hz⟩ := hm0ne
            have hz0 : z ∈ side (n := 26) D a 0 := horIn_sub (opnd D a 0) m0 hrm0 hz
            have hz1 : z ∈ side (n := 26) D a 1 := horIn_sub (opnd D a 1) m0 hrm1 hz
            exact G3.ne_of_adj (hside_adj a ha z hz0 z hz1) rfl
        obtain ⟨a1, ha1, b1, m1, hm1, hv1s, hrm1, hm1ne⟩ := hmix_of v1 hv1
        obtain ⟨a2, ha2, b2, m2, hm2, hv2s, hrm2, _⟩ := hmix_of v2 hv2
        have hm12 : m1 = m2 := Finset.card_le_one.mp hMle1 m1 hm1 m2 hm2
        subst hm12
        obtain ⟨z, hz⟩ := hm1ne
        have hz1 : z ∈ side (n := 26) D a1 (1 - b1) := horIn_sub _ m1 hrm1 hz
        have hz2 : z ∈ side (n := 26) D a2 (1 - b2) := horIn_sub _ m1 hrm2 hz
        have hadj1 : G3.Adj v1 z := by
          fin_cases b1
          · exact hside_adj a1 ha1 v1 hv1s z hz1
          · exact (hside_adj a1 ha1 z hz1 v1 hv1s).symm
        have hadj2 : G3.Adj v2 z := by
          fin_cases b2
          · exact hside_adj a2 ha2 v2 hv2s z hz2
          · exact (hside_adj a2 ha2 z hz2 v2 hv2s).symm
        have hzw : z = w := by
          have h1 : z ∈ Finset.univ.filter (fun u : Fin 26 => G3.Adj v1 u ∧ G3.Adj v2 u) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj1, hadj2⟩
          have h2 : w ∈ Finset.univ.filter (fun u : Fin 26 => G3.Adj v1 u ∧ G3.Adj v2 u) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv1.symm, hv2.symm⟩
          exact Finset.card_le_one.mp (hG3_4free v1 v2 hv12) z h1 w h2
        rw [hzw] at hz1
        have hstar1 : s(w, v1) ∈ starEdges G3 D := by
          fin_cases b1
          · rw [Sym2.eq_swap]; exact hstar_mk a1 ha1 v1 hv1s w hz1
          · exact hstar_mk a1 ha1 w hz1 v1 hv1s
        exact (Finset.mem_sdiff.mp (hw v1 hv1)).2 hstar1
      exact hJunk2NoC G3 D hG3 hD_least hD_top hD_sz hJ2 hC0 hU5 hM1 h5U'
    · have hC1 : 1 ≤ (centreless G3 D).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC0)
      have hU5 : 5 ≤ (Ustar G3 D).card := by omega
      exact hJunk2WithC G3 D hG3 hD_least hD_top hD_sz hJ2 hC1 hU5 h5U
