import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_384 :
    ∀ (β : Type) (e : β → List Bool) (f : List Bool → β),
      PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => e (f x)) ↔
      PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) e f := by
  intro β e f
  constructor <;> rintro ⟨machine⟩ <;>
    exact ⟨⟨machine.toTM2ComputableAux, machine.time, machine.outputsFun⟩⟩
