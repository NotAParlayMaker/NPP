import Mathlib
import PEqualNP.Defs

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

theorem PEqualNP.Outside.L_meta_495 :
    ∀ (φ : CNF) (e : ℕ → ℕ),
      (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx
        (fun o => o.any (fun l => l.1 == z))) →
      ∀ z ∈ vars φ, (∃ l : Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? =
        some (some l) ∧ l.1 = z) ∧ ∀ g < e z, ∀ l : Literal,
        (φ.flatMap (fun c => c.map some ++ [none]))[g]? = some (some l) → l.1 ≠ z := by
  intro φ e he z hz
  let items := φ.flatMap (fun c => c.map some ++ [none])
  let p (o : Option Literal) := o.any (fun l => l.1 == z)
  change (∃ l : Literal, items[e z]? = some (some l) ∧ l.1 = z) ∧
    ∀ g < e z, ∀ l : Literal, items[g]? = some (some l) → l.1 ≠ z
  rw [show e z = items.findIdx p from he z]
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map] at hz
  obtain ⟨c,hc,l,hl,heq⟩ := hz
  have occurs : some l ∈ items := List.mem_flatMap.mpr
    ⟨c,hc,List.mem_append_left _ (List.mem_map.mpr ⟨l,hl,rfl⟩)⟩
  have inRange : items.findIdx p < items.length :=
    List.findIdx_lt_length_of_exists ⟨some l,occurs,by simp [p,heq]⟩
  constructor
  · have hit := List.findIdx_getElem (w := inRange)
    cases h : items[items.findIdx p] with
    | none => simp [h,p] at hit
    | some a => exact ⟨a,by rw [List.getElem?_eq_getElem inRange,h],by simpa [h,p] using hit⟩
  · intro g hg a ha
    have hmiss := List.not_of_lt_findIdx hg
    rw [List.getElem?_eq_getElem (hg.trans inRange)] at ha
    have eq := Option.some.inj ha
    simpa [eq,p] using hmiss

