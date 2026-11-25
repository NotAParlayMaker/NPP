import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The 52 flags and 468 distinct negative rows give columns in the Boolean
-- lattice on 520 coordinates.  The integer stores 40 cyclic seed rows in
-- 26-bit blocks; each block develops to 13 simultaneous translations.
--
-- Guess just an unordered dictionary of at most 61 free columns, in addition
-- to the prescribed output and a symmetry representative for the first gate.
-- A dictionary succeeds iff the closure of the input columns under binary
-- meets and joins *inside this dictionary* reaches the output.  The universal
-- cut condition expresses that closure test without any wires or gate order.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.R_meta_2625_625
    (compile :
    ∀ (n : ℕ) (R : Type) (x : R → Fin n → Bool) (ss : List (R → Bool)),
      (∀ (pre : List (R → Bool)) (v : R → Bool) (post : List (R → Bool)),
        ss = pre ++ v :: post →
          (let avail := (List.ofFn (fun i : Fin n => fun r : R => x r i)) ++ pre;
           ∃ a ∈ avail, ∃ b ∈ avail,
             v = (fun r => a r && b r) ∨ v = (fun r => a r || b r))) →
      ∃ C : Circuit, Monotone2 C ∧ C.size = ss.length ∧
        ∀ r : R, C.wires (List.ofFn (x r)) =
          (List.ofFn (x r)) ++ ss.map (fun s => s r))
    (linear :
    ∀ (R : Type) (base : List (R → Bool)) (F : Finset (R → Bool)) (goal : R → Bool),
    goal ∈ F →
    (∀ U : Finset (R → Bool), U ⊆ F → goal ∉ U →
      ∃ v ∈ F, v ∉ U ∧ ∃ a : R → Bool, (a ∈ base ∨ a ∈ U) ∧
        ∃ b : R → Bool, (b ∈ base ∨ b ∈ U) ∧
          (v = (fun r => a r && b r) ∨ v = (fun r => a r || b r))) →
    ∃ ss : List (R → Bool), ss.length ≤ F.card ∧ goal ∈ ss ∧
      ∀ (pre : List (R → Bool)) (v : R → Bool) (post : List (R → Bool)),
        ss = pre ++ v :: post →
        (let avail := base ++ pre; ∃ a ∈ avail, ∃ b ∈ avail,
          v = (fun r => a r && b r) ∨ v = (fun r => a r || b r)))
    (search :
      let bits : ℕ := 3039053630815613945006974869036603982375996890462778088458099590663800415382429076832958578102880203986374511108268226431870050235481086142087432178223638673248873883833120745629007479098173280420763559937702275013626224379359378766342823507785147225990703565407617646914155020309754868247787482635024486824419329
      let input := fun (r : Fin 520) (k : Fin 26) =>
        bits.testBit (26 * (r.val / 13) + 13 * (k.val / 13) + (k.val + r.val) % 13)
      let goal := fun r : Fin 520 => decide (r.val < 52)
      let col := fun (k : Fin 26) (r : Fin 520) => input r k
      ∃ (j : Fin 4) (H : Finset (Fin 520 → Bool)), H.card ≤ 61 ∧
      (let k := ([13, 1, 13, 14] : List (Fin 26)).getD j.val 0
      let seed := if j.val = 0 then (fun r => col 0 r && col k r)
                  else (fun r => col 0 r || col k r)
      let F := insert seed (insert goal H)
       ∀ U : Finset (Fin 520 → Bool), U ⊆ F → goal ∉ U →
         ∃ v ∈ F, v ∉ U ∧
           (let ok := fun a : Fin 520 → Bool => a ∈ List.ofFn col ∨ a ∈ U
            ∃ a, ok a ∧ ∃ b, ok b ∧
              (v = (fun r => a r && b r) ∨ v = (fun r => a r || b r))))) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), (∃ x7 ∈ x1, x5 = x6 + x7) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 (x3 x5 x7 x9 x10) = Bool.false := by
  intro D reps row
  let bits : ℕ := 3039053630815613945006974869036603982375996890462778088458099590663800415382429076832958578102880203986374511108268226431870050235481086142087432178223638673248873883833120745629007479098173280420763559937702275013626224379359378766342823507785147225990703565407617646914155020309754868247787482635024486824419329
  let input := fun (r : Fin 520) (k : Fin 26) =>
    bits.testBit (26 * (r.val / 13) + 13 * (k.val / 13) + (k.val + r.val) % 13)
  let goal := fun r : Fin 520 => decide (r.val < 52)
  let col := fun (k : Fin 26) (r : Fin 520) => input r k
  obtain ⟨j, H, hH, cut⟩ := search
  let k := ([13, 1, 13, 14] : List (Fin 26)).getD j.val 0
  let seed := if j.val = 0 then (fun r => col 0 r && col k r)
              else (fun r => col 0 r || col k r)
  let F := insert seed (insert goal H)
  have hcap : F.card ≤ 63 := by
    calc
      F.card ≤ (insert goal H).card + 1 := Finset.card_insert_le _ _
      _ ≤ (H.card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ 63 := by omega
  obtain ⟨ss, hn, hout, hgen⟩ := linear (Fin 520) (List.ofFn col) F goal
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) cut
  obtain ⟨B, hm, hs, hw⟩ := compile 26 (Fin 520) input ss hgen
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hout
  let C : Circuit := ⟨B.gates, 26 + i⟩
  have labels (r : Fin 520) : circuitFun 26 C (input r) = goal r := by
    change (B.wires (List.ofFn (input r))).getD (26 + i) false = _
    rw [hw r, List.getD_append_right _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, he]
  refine ⟨C, hm, hs.le.trans (hn.trans hcap), ?_, ?_⟩
  · intro p l hit
    let pos := fun (p l : Fin 13) => (⟨(13 * (if p-l = 0 then 0 else if p-l = 1 then 1 else if p-l = 3 then 2 else 3) + (-l).val) % 520,
      Nat.mod_lt _ (by decide)⟩ : Fin 520)
    have chk : ∀ p l : Fin 13, (∃ d ∈ D, p = l + d) →
        goal (pos p l) = true ∧ ∀ k : Fin 26,
        input (pos p l) k = decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l) := by
      dsimp only [input, bits, goal, pos, D]
      decide +kernel
    obtain ⟨hl, hk⟩ := chk p l hit
    exact (congrArg _ (funext hk).symm).trans ((labels (pos p l)).trans hl)
  · intro rep hrep a ha b f
    let as : List (Fin 13) := [1,3,9]
    let start := fun (i : Fin 8) (j : Fin 3) (f : Bool) =>
      ((1565415907984930045796654651713523468865117495576223451084808259585288980155129451807261121726516608250186748474636491653540799097120747201561652 : ℕ) >>> (10 * (i.val * 6 + j.val * 2 + (if f then 1 else 0)))) % 1024
    let neg := fun (i : Fin 8) (j : Fin 3) (b : Fin 13) (f : Bool) =>
      (⟨(13 * (start i j f / 13) + (start i j f + (if j = 0 then 1 else if j = 1 then 9 else 3) * b.val) % 13) % 520, Nat.mod_lt _ (by decide)⟩ : Fin 520)
    have chk : ∀ (i : Fin 8) (j : Fin 3) (b : Fin 13) (f : Bool),
        goal (neg i j b f) = false ∧ ∀ k : Fin 26,
        input (neg i j b f) k = row (reps.get i) (as.get j) b f k := by
      dsimp only [input, bits, goal, neg, start, reps, row, as]
      decide +kernel
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hrep
    change a ∈ as at ha
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ha
    obtain ⟨hl, hk⟩ := chk i j b f
    exact (congrArg _ (funext hk).symm).trans ((labels (neg i j b f)).trans hl)
