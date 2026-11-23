import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta562

open PEqualNP.AndCount
open PEqualNP.AndCount.AndCountCircuit

variable {n : ℕ}

lemma sideTrue_mono {U V : Finset (Fin n)} (hUV : U ⊆ V) {B : Finset (Fin n)}
    {F : Finset (Fin k)} {i : Fin k} {val val' : Fin k → Bool}
    (hval : ∀ j, val j = true → val' j = true) :
    sideTrue U B F i val = true → sideTrue V B F i val' = true := by
  intro h
  simp [sideTrue] at h ⊢
  rcases h with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hval j hjv⟩

lemma gateValFuel_mono_U (C : AndCountCircuit n) {U V : Finset (Fin n)} (hUV : U ⊆ V) :
    ∀ d (i : Fin C.size), gateValFuel C U d i = true → gateValFuel C V d i = true
  | 0, i, h => by cases h
  | d + 1, i, h => by
      simp only [gateValFuel] at h ⊢
      rw [Bool.and_eq_true] at h ⊢
      exact ⟨sideTrue_mono hUV (fun j hj => gateValFuel_mono_U C hUV d j hj) h.1,
        sideTrue_mono hUV (fun j hj => gateValFuel_mono_U C hUV d j hj) h.2⟩

lemma gateValFuel_mono_d (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d d', d ≤ d' → ∀ (i : Fin C.size),
      gateValFuel C U d i = true → gateValFuel C U d' i = true
  | 0, 0, hdd', i, h => h
  | 0, d' + 1, hdd', i, h => by cases h
  | d + 1, 0, hdd', i, h => by omega
  | d + 1, e + 1, hdd', i, h => by
      have hde : d ≤ e := by omega
      simp only [gateValFuel] at h ⊢
      rw [Bool.and_eq_true] at h ⊢
      exact ⟨sideTrue_mono (fun _ hx => hx)
          (fun j hj => gateValFuel_mono_d C U d e hde j hj) h.1,
        sideTrue_mono (fun _ hx => hx)
          (fun j hj => gateValFuel_mono_d C U d e hde j hj) h.2⟩

lemma gateVal_left_true (C : AndCountCircuit n) (i : Fin C.size) :
    C.gateVal Finset.univ i = true →
      (C.leftVars i).Nonempty ∨
        ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal Finset.univ j = true := by
  intro h
  have hpos : 0 < C.size := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hs : C.size = (C.size - 1) + 1 := by omega
  unfold PEqualNP.AndCount.AndCountCircuit.gateVal at h
  rw [hs] at h
  simp only [PEqualNP.AndCount.AndCountCircuit.gateValFuel] at h
  have hboth : sideTrue Finset.univ (C.leftVars i) (C.leftGates i) i
      (gateValFuel C Finset.univ (C.size - 1)) = true ∧
      sideTrue Finset.univ (C.rightVars i) (C.rightGates i) i
      (gateValFuel C Finset.univ (C.size - 1)) = true := by simpa using h
  have hleft : sideTrue Finset.univ (C.leftVars i) (C.leftGates i) i
      (gateValFuel C Finset.univ (C.size - 1)) = true := hboth.1
  have hleftP : ((∃ v ∈ C.leftVars i, v ∈ (Finset.univ : Finset (Fin n))) ∨
      ∃ j ∈ C.leftGates i, j < i ∧
        gateValFuel C Finset.univ (C.size - 1) j = true) := by
    unfold sideTrue at hleft
    exact of_decide_eq_true hleft
  rcases hleftP with ⟨v, hvB, _⟩ | ⟨j, hjF, hji, hjv⟩
  · exact Or.inl ⟨v, hvB⟩
  · exact Or.inr ⟨j, hjF, hji, by
      simpa [PEqualNP.AndCount.AndCountCircuit.gateVal] using
        gateValFuel_mono_d C Finset.univ (C.size - 1) C.size (by omega) j hjv⟩

lemma gateVal_right_true (C : AndCountCircuit n) (i : Fin C.size) :
    C.gateVal Finset.univ i = true →
      (C.rightVars i).Nonempty ∨
        ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal Finset.univ j = true := by
  intro h
  have hpos : 0 < C.size := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hs : C.size = (C.size - 1) + 1 := by omega
  unfold PEqualNP.AndCount.AndCountCircuit.gateVal at h
  rw [hs] at h
  simp only [PEqualNP.AndCount.AndCountCircuit.gateValFuel] at h
  have hboth : sideTrue Finset.univ (C.leftVars i) (C.leftGates i) i
      (gateValFuel C Finset.univ (C.size - 1)) = true ∧
      sideTrue Finset.univ (C.rightVars i) (C.rightGates i) i
      (gateValFuel C Finset.univ (C.size - 1)) = true := by simpa using h
  have hright : sideTrue Finset.univ (C.rightVars i) (C.rightGates i) i
      (gateValFuel C Finset.univ (C.size - 1)) = true := hboth.2
  have hrightP : ((∃ v ∈ C.rightVars i, v ∈ (Finset.univ : Finset (Fin n))) ∨
      ∃ j ∈ C.rightGates i, j < i ∧
        gateValFuel C Finset.univ (C.size - 1) j = true) := by
    unfold sideTrue at hright
    exact of_decide_eq_true hright
  rcases hrightP with ⟨v, hvB, _⟩ | ⟨j, hjF, hji, hjv⟩
  · exact Or.inl ⟨v, hvB⟩
  · exact Or.inr ⟨j, hjF, hji, by
      simpa [PEqualNP.AndCount.AndCountCircuit.gateVal] using
        gateValFuel_mono_d C Finset.univ (C.size - 1) C.size (by omega) j hjv⟩

lemma gateVal_false_of_univ_false (C : AndCountCircuit n) {U : Finset (Fin n)}
    (i : Fin C.size) (hfalse : C.gateVal Finset.univ i = false) :
    C.gateVal U i = false := by
  by_contra hn
  have htrue : C.gateVal U i = true := by
    cases hU : C.gateVal U i <;> simp_all
  have hf : gateValFuel C U C.size i = true := by
    simpa [PEqualNP.AndCount.AndCountCircuit.gateVal] using htrue
  have hfu : gateValFuel C Finset.univ C.size i = true :=
    gateValFuel_mono_U C (Finset.subset_univ U) C.size i hf
  have ht : C.gateVal Finset.univ i = true := by
    simpa [PEqualNP.AndCount.AndCountCircuit.gateVal] using hfu
  simp [ht] at hfalse

lemma no_good_fin0 (C : AndCountCircuit 0) :
    ∀ i : Fin C.size, C.gateVal Finset.univ i = false := by
  have h : ∀ m (hm : m < C.size), C.gateVal Finset.univ ⟨m, hm⟩ = false := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
        intro hm
        by_contra hn
        have htrue : C.gateVal Finset.univ ⟨m, hm⟩ = true := by
          cases hv : C.gateVal Finset.univ ⟨m, hm⟩ <;> simp_all
        have hl := gateVal_left_true C ⟨m, hm⟩ htrue
        rcases hl with ⟨v, hvB⟩ | ⟨j, hjF, hjlt, hjgood⟩
        · exact Fin.elim0 v
        · have hjfalse : C.gateVal Finset.univ ⟨j.val, j.isLt⟩ = false :=
            ih j.val hjlt j.isLt
          have huniv0 : (Finset.univ : Finset (Fin 0)) = ∅ := by
            ext x
            exact Fin.elim0 x
          have hjfalse' : C.gateVal Finset.univ j = false := by
            simpa using hjfalse
          have hjfalse0 : C.gateVal (∅ : Finset (Fin 0)) j = false := by
            simpa [huniv0] using hjfalse'
          simp [hjfalse0] at hjgood
  intro i
  simpa using h i.val i.isLt

end PEqualNP.Outside.Meta562

open PEqualNP.AndCount
open PEqualNP.AndCount.AndCountCircuit
open PEqualNP.Outside.Meta562

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_562 :
    ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n),
    C.WellFormed →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n,
        C'.WellFormed ∧ C'.size ≤ C.size ∧ (∀ U : Finset (Fin n), C'.eval U = C.eval U) ∧
        (∀ i : Fin C'.size, ((C'.leftVars i).Nonempty ∨ (C'.leftGates i).Nonempty) ∧
          ((C'.rightVars i).Nonempty ∨ (C'.rightGates i).Nonempty)) ∧
        ∀ i : Fin C'.size, C'.gateVal Finset.univ i = true := by
  intro n C hWF
  by_cases hn : n = 0
  · subst n
    let C' : PEqualNP.AndCount.AndCountCircuit 0 :=
      { size := 0
        leftVars := fun i => Fin.elim0 i
        leftGates := fun i => Fin.elim0 i
        rightVars := fun i => Fin.elim0 i
        rightGates := fun i => Fin.elim0 i
        outVars := C.outVars
        outGates := ∅ }
    refine ⟨C', ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · simp [C']
    · intro U
      have hno : ¬ ∃ j ∈ C.outGates, C.gateVal U j = true := by
        rintro ⟨j, hjG, hjv⟩
        have hf : C.gateVal U j = false := gateVal_false_of_univ_false C j (no_good_fin0 C j)
        simp [hf] at hjv
      simp [PEqualNP.AndCount.AndCountCircuit.eval, C', hno]
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  · let v0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let good : Fin C.size → Prop := fun i => C.gateVal Finset.univ i = true
    let C' : PEqualNP.AndCount.AndCountCircuit n :=
      { size := C.size
        leftVars := fun i => if good i then C.leftVars i else {v0}
        leftGates := fun i => (C.leftGates i).filter good
        rightVars := fun i => if good i then C.rightVars i else {v0}
        rightGates := fun i => (C.rightGates i).filter good
        outVars := C.outVars
        outGates := (C.outGates).filter good }
    have hfuel_eq : ∀ (U : Finset (Fin n)) (d : ℕ), d ≤ C.size →
        ∀ (i : Fin C.size), good i →
          gateValFuel C' U d i = gateValFuel C U d i := by
      intro U d
      induction d with
      | zero =>
          intro hd i hi
          rfl
      | succ d ih =>
          intro hd i hi
          have hd' : d ≤ C.size := by omega
          have H := ih hd'
          have side_eq : ∀ {B B' : Finset (Fin n)} {F F' : Finset (Fin C.size)},
              B' = B → F' = F.filter good →
              sideTrue U B' F' i (gateValFuel C' U d) =
                sideTrue U B F i (gateValFuel C U d) := by
            intro B B' F F' hB hF
            subst B'
            subst F'
            have hiff :
                ((∃ v ∈ B, v ∈ U) ∨
                    ∃ j ∈ F.filter good, j < i ∧ gateValFuel C' U d j = true) ↔
                ((∃ v ∈ B, v ∈ U) ∨
                    ∃ j ∈ F, j < i ∧ gateValFuel C U d j = true) := by
              constructor
              · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩)
                · exact Or.inl ⟨v, hvB, hvU⟩
                · have hjgood : good j := (Finset.mem_filter.mp hjF).2
                  have hjF0 : j ∈ F := (Finset.mem_filter.mp hjF).1
                  have hjval : gateValFuel C U d j = true := by
                    rw [← H j hjgood]
                    exact hjv
                  exact Or.inr ⟨j, hjF0, hji, hjval⟩
              · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF0, hji, hjv⟩)
                · exact Or.inl ⟨v, hvB, hvU⟩
                · have hjgood : good j := by
                    have hjfull : gateValFuel C U C.size j = true :=
                      gateValFuel_mono_d C U d C.size hd' j hjv
                    have hjuniv : gateValFuel C Finset.univ C.size j = true :=
                      gateValFuel_mono_U C (Finset.subset_univ U) C.size j hjfull
                    simpa [good, PEqualNP.AndCount.AndCountCircuit.gateVal] using hjuniv
                  have hjval' : gateValFuel C' U d j = true := by
                    rw [H j hjgood]
                    exact hjv
                  exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨hjF0, hjgood⟩, hji, hjval'⟩
            unfold sideTrue
            exact decide_eq_decide.mpr hiff
          simp only [gateValFuel]
          rw [side_eq (B := C.leftVars i) (B' := C'.leftVars i)
                (F := C.leftGates i) (F' := C'.leftGates i)
                (by simp [C', hi]) (by rfl),
              side_eq (B := C.rightVars i) (B' := C'.rightVars i)
                (F := C.rightGates i) (F' := C'.rightGates i)
                (by simp [C', hi]) (by rfl)]
    have hgood_eq : ∀ (U : Finset (Fin n)) (i : Fin C.size),
        good i → C'.gateVal U i = C.gateVal U i := by
      intro U i hi
      simpa [PEqualNP.AndCount.AndCountCircuit.gateVal] using
        hfuel_eq U C.size (le_refl C.size) i hi
    refine ⟨C', ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      constructor
      · intro j hj
        have hj0 : j ∈ C.leftGates i := (Finset.mem_filter.mp (by simpa [C'] using hj)).1
        exact (hWF i).1 j hj0
      · intro j hj
        have hj0 : j ∈ C.rightGates i := (Finset.mem_filter.mp (by simpa [C'] using hj)).1
        exact (hWF i).2 j hj0
    · simp [C']
    · intro U
      have hout : (∃ j ∈ (C.outGates).filter good, C'.gateVal U j = true) ↔
          (∃ j ∈ C.outGates, C.gateVal U j = true) := by
        constructor
        · rintro ⟨j, hjF, hjv⟩
          have hj0 : j ∈ C.outGates := (Finset.mem_filter.mp hjF).1
          have hjgood : good j := (Finset.mem_filter.mp hjF).2
          have hjvC : C.gateVal U j = true := by
            rw [← hgood_eq U j hjgood]
            exact hjv
          exact ⟨j, hj0, hjvC⟩
        · rintro ⟨j, hj0, hjvC⟩
          have hjgood : good j := by
            have hf : gateValFuel C U C.size j = true := by
              simpa [PEqualNP.AndCount.AndCountCircuit.gateVal] using hjvC
            have hfu : gateValFuel C Finset.univ C.size j = true :=
              gateValFuel_mono_U C (Finset.subset_univ U) C.size j hf
            simpa [good, PEqualNP.AndCount.AndCountCircuit.gateVal] using hfu
          have hjvC' : C'.gateVal U j = true := by
            rw [hgood_eq U j hjgood]
            exact hjvC
          exact ⟨j, Finset.mem_filter.mpr ⟨hj0, hjgood⟩, hjvC'⟩
      simp only [PEqualNP.AndCount.AndCountCircuit.eval]
      change decide ((∃ v ∈ C.outVars, v ∈ U) ∨
          ∃ j ∈ (C.outGates).filter good, C'.gateVal U j = true) =
        decide ((∃ v ∈ C.outVars, v ∈ U) ∨
          ∃ j ∈ C.outGates, C.gateVal U j = true)
      have hiffall : ((∃ v ∈ C.outVars, v ∈ U) ∨
          ∃ j ∈ (C.outGates).filter good, C'.gateVal U j = true) ↔
          ((∃ v ∈ C.outVars, v ∈ U) ∨
            ∃ j ∈ C.outGates, C.gateVal U j = true) := by
        constructor
        · intro h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (hout.mp h)
        · intro h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (hout.mpr h)
      exact decide_eq_decide.mpr hiffall
    · intro i
      constructor
      · by_cases hi : good i
        · by_cases hv : (C.leftVars i).Nonempty
          · left
            simpa [C', hi] using hv
          · right
            have hl := gateVal_left_true C i hi
            rcases hl with ⟨v, hvB⟩ | ⟨j, hjF, hjlt, hjgood⟩
            · exact False.elim (hv ⟨v, hvB⟩)
            · refine ⟨j, ?_⟩
              simpa [C'] using
                (Finset.mem_filter.mpr ⟨hjF, hjgood⟩ : j ∈ (C.leftGates i).filter good)
        · left
          simp [C', hi]
      · by_cases hi : good i
        · by_cases hv : (C.rightVars i).Nonempty
          · left
            simpa [C', hi] using hv
          · right
            have hr := gateVal_right_true C i hi
            rcases hr with ⟨v, hvB⟩ | ⟨j, hjF, hjlt, hjgood⟩
            · exact False.elim (hv ⟨v, hvB⟩)
            · refine ⟨j, ?_⟩
              simpa [C'] using
                (Finset.mem_filter.mpr ⟨hjF, hjgood⟩ : j ∈ (C.rightGates i).filter good)
        · left
          simp [C', hi]
    · intro i
      by_cases hi : good i
      · have h := hgood_eq Finset.univ i hi
        rw [h]
        exact hi
      · have hpos : 1 ≤ C.size :=
          Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) i.isLt)
        have hone : gateValFuel C' Finset.univ 1 i = true := by
          simp [PEqualNP.AndCount.AndCountCircuit.gateValFuel,
            PEqualNP.AndCount.AndCountCircuit.sideTrue, C', hi]
        have hfull := gateValFuel_mono_d C' Finset.univ 1 C.size hpos i hone
        simpa [PEqualNP.AndCount.AndCountCircuit.gateVal] using hfull
