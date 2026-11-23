import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1185_aux

open PEqualNP.CircuitLowerBounds

def c : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.and, [5, 13]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k (a0 a1 a2 a3 a4 a5 a6 a7 : Bool) :
    c.eval [a0, a1, a2, a3, a4, a5, a6, a7] =
      ((a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a1 && a4) || (a5 && a6) || (a5 && a7)) := by
  dsimp only [c, Circuit.eval, Circuit.wires, GateOp.eval, List.foldl, List.map,
    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.all, List.any, id_eq]
  simp only [Bool.and_true, Bool.or_false, Bool.and_or_distrib_left, Bool.or_assoc]

theorem proof : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6) || (x 5 && x 7)) x := by
  refine ⟨c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

end PEqualNP.Outside.L_meta_1185_aux

theorem PEqualNP.Outside.L_meta_1185 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6) || (x 5 && x 7)) x :=
  PEqualNP.Outside.L_meta_1185_aux.proof
