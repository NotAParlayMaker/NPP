import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9361_aux

def rows : List ℕ := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def data : List (ℕ × ℕ) := [(1163360, 394120), (133195, 578064), (1119256, 286882), (532780, 215105), (2738, 1744900), (175232, 524597), (819221, 79168), (279814, 1120296), (1066753, 268302), (790976, 1115651), (31233, 32862), (336641, 527434), (214148, 1313072), (700928, 1237), (393810, 1610880), (1450116, 36129)]

def decode (m : ℕ) : Finset (Fin 21) :=
  Finset.univ.filter (fun i => m.testBit i.val = true)

def rect (q : ℕ × ℕ) : Finset (Fin 21) × Finset (Fin 21) :=
  (decode q.1, decode q.2)

def cover : List (Finset (Fin 21) × Finset (Fin 21)) := data.map rect

def accepts (i j : Fin 21) : Bool :=
  data.any (fun q => q.1.testBit i.val && q.2.testBit j.val)

def verify : Bool :=
  (List.finRange 21).all (fun i => (List.finRange 21).all (fun j =>
    decide (accepts i j = !((rows.getD i.val 0).testBit j.val))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem verified : verify = true := by decide +kernel

theorem equivalent (i j : Fin 21) :
    (∃ q ∈ data, q.1.testBit i.val = true ∧ q.2.testBit j.val = true) ↔
      (rows.getD i.val 0).testBit j.val = false := by
  have row := List.all_eq_true.mp verified i (by simp)
  have test := of_decide_eq_true (List.all_eq_true.mp row j (by simp))
  have hit : accepts i j = true ↔ (rows.getD i.val 0).testBit j.val = false := by
    rw [test]
    cases (rows.getD i.val 0).testBit j.val <;> decide
  simpa only [accepts, List.any_eq_true, Bool.and_eq_true] using hit

theorem covered :
    (∀ r ∈ cover, ∀ i ∈ r.1, ∀ j ∈ r.2, (rows.getD i.val 0).testBit j.val = false) ∧
      ∀ (i j : Fin 21), (rows.getD i.val 0).testBit j.val = false →
        ∃ r ∈ cover, i ∈ r.1 ∧ j ∈ r.2 := by
  constructor
  · intro r hr i hi j hj
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    apply (equivalent i j).mp
    exact ⟨q, hq, by simpa [rect, decode] using hi, by simpa [rect, decode] using hj⟩
  · intro i j valid
    obtain ⟨q, hq, hi, hj⟩ := (equivalent i j).mpr valid
    refine ⟨rect q, List.mem_map.mpr ⟨q, hq, rfl⟩, ?_, ?_⟩
    · simpa [rect, decode] using hi
    · simpa [rect, decode] using hj

end PEqualNP.Outside.L_meta_9361_aux

theorem PEqualNP.Outside.L_meta_9361 : ∃ L : List (Finset (Fin 21) × Finset (Fin 21)), L.length ≤ 17 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 21) (j : Fin 21), (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  exact ⟨PEqualNP.Outside.L_meta_9361_aux.cover, by decide, PEqualNP.Outside.L_meta_9361_aux.covered⟩
