import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic.Push
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_734 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.Colorable 2 →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  (∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard) →
  ∀ T : Set (Fin n), T.ncard ≤ 5 →
    (∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) →
      ∃ t ∈ T, t ∈ I) →
    ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  classical
  intro n G hcolor hcycle hdeg T hT hmeet
  obtain ⟨col⟩ := hcolor
  by_contra hclosed
  push_neg at hclosed
  let f : Fin n → Fin n := fun v => if h : v ∈ T then Classical.choose (hclosed v h) else v
  have hf (v : Fin n) (hv : v ∈ T) : G.Adj v (f v) ∧ f v ∉ T := by
    simpa only [f, dif_pos hv] using Classical.choose_spec (hclosed v hv)
  let F := T.toFinset
  have hF : F.card ≤ 5 := by simpa only [F, ← Set.ncard_eq_toFinset_card'] using hT
  have hsmall : ∃ c : Fin 2, (F.filter (fun v => col v = c)).card ≤ 2 := by
    by_cases h0 : (F.filter (fun v => col v = 0)).card ≤ 2
    · exact ⟨0, h0⟩
    · refine ⟨1, ?_⟩
      have hp := Finset.card_filter_add_card_filter_not (s := F) (p := fun v => col v = 0)
      have he : F.filter (fun v => ¬ col v = 0) = F.filter (fun v => col v = 1) := by
        ext v
        simp only [Finset.mem_filter]
        have hv := (col v).isLt
        constructor <;> rintro ⟨h, hc⟩ <;> exact ⟨h, by omega⟩
      rw [he] at hp
      omega
  obtain ⟨c, hc⟩ := hsmall
  let B := (F.filter (fun v => col v = c)).image f
  have hBcard : B.card ≤ 2 := (Finset.card_image_le).trans hc
  have hB (b : Fin n) (hb : b ∈ B) : col b ≠ c ∧ b ∉ T := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hvT, hvc⟩ := Finset.mem_filter.mp hv
    have hh := hf v (by simpa [F] using hvT)
    exact ⟨fun he => col.valid hh.1 (hvc.trans he.symm), hh.2⟩
  let A : Set (Fin n) := {a | col a = c ∧ ∀ b ∈ B, ¬ G.Adj a b}
  let Y : Set (Fin n) := {y | col y ≠ c ∧ ∀ a ∈ A, ¬ G.Adj y a}
  have hBY : ∀ b ∈ B, b ∈ Y := by
    intro b hb
    exact ⟨(hB b hb).1, fun a ha hab => ha.2 b hb hab.symm⟩
  have hTA : ∀ a ∈ T, a ∉ A := by
    intro a ha hA
    have hb : f a ∈ B := Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
      ⟨by simpa [F] using ha, hA.1⟩, rfl⟩
    exact hA.2 (f a) hb (hf a ha).1
  have hTY : ∀ y ∈ T, y ∉ Y := by
    intro y hy hY
    have hcovered : ∀ a : Fin n, G.Adj y a → ∃ b ∈ B, G.Adj a b := by
      intro a hya
      have hac : col a = c := by
        have := col.valid hya
        have := hY.1
        have := (col a).isLt
        have := (col y).isLt
        have := c.isLt
        omega
      by_contra hn
      push_neg at hn
      exact hY.2 a ⟨hac, hn⟩ hya
    let pick : Fin n → Fin n := fun a => if h : G.Adj y a then
      Classical.choose (hcovered a h) else y
    have hp (a : Fin n) (ha : G.Adj y a) : pick a ∈ B ∧ G.Adj a (pick a) := by
      simpa only [pick, dif_pos ha] using Classical.choose_spec (hcovered a ha)
    have hinj : Set.InjOn pick {a | G.Adj y a} := by
      intro a ha d hd had
      have hh := hcycle y a (pick a) d ha (hp a ha).2
        (had ▸ (hp d hd).2.symm) hd.symm
      rcases hh with he | he
      · exact False.elim ((hB (pick a) (hp a ha).1).2 (he ▸ hy))
      · exact he
    have hle : {a | G.Adj y a}.ncard ≤ (↑B : Set (Fin n)).ncard :=
      Set.ncard_le_ncard_of_injOn pick (fun a ha => (hp a ha).1) hinj
    have hb : (↑B : Set (Fin n)).ncard = B.card := Set.ncard_coe_finset B
    have hd := hdeg y
    omega
  have hind : ∀ u ∈ A ∪ Y, ∀ v ∈ A ∪ Y, ¬ G.Adj u v := by
    intro u hu v hv huv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact col.valid huv (hu.1.trans hv.1.symm)
    · exact hv.2 u hu huv.symm
    · exact hu.2 v hv huv
    · have := col.valid huv
      have := hu.1
      have := hv.1
      have := (col u).isLt
      have := (col v).isLt
      have := c.isLt
      omega
  have hmax : ∀ v, v ∉ A ∪ Y → ∃ u ∈ A ∪ Y, G.Adj v u := by
    intro v hv
    by_cases hvc : col v = c
    · have hn : ¬ ∀ b ∈ B, ¬ G.Adj v b := fun hn => hv (Or.inl ⟨hvc, hn⟩)
      push_neg at hn
      obtain ⟨b, hb, h⟩ := hn
      exact ⟨b, Or.inr (hBY b hb), h⟩
    · have hn : ¬ ∀ a ∈ A, ¬ G.Adj v a := fun hn => hv (Or.inr ⟨hvc, hn⟩)
      push_neg at hn
      obtain ⟨a, ha, h⟩ := hn
      exact ⟨a, Or.inl ha, h⟩
  obtain ⟨t, ht, hi⟩ := hmeet (A ∪ Y) hind hmax
  exact hi.elim (hTA t ht) (hTY t ht)
