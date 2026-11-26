import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5997_2 :
    (∃ (G : SimpleGraph (Fin 26)) (hdec : DecidableRel G.Adj),
      ∀ x : Fin 26 → Bool,
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x =
          decide (∃ (x4 : Fin 13) (x5 : Fin 13),
            (x4 = x5 ∨ x4 = x5 + 1 ∨ x4 = x5 + 3 ∨ x4 = x5 + 9) ∧
              x4 ≠ 0 ∧ x (Fin.castAdd 13 x4) = true ∧ x (Fin.natAdd 13 x5) = true)) →
    (∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ x : Fin 26 → Bool,
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x =
          decide (∃ (x4 : Fin 13) (x5 : Fin 13),
            (x4 = x5 ∨ x4 = x5 + 1 ∨ x4 = x5 + 3 ∨ x4 = x5 + 9) ∧
              x4 ≠ 0 ∧ x (Fin.castAdd 13 x4) = true ∧ x (Fin.natAdd 13 x5) = true)) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ x : Fin 26 → Bool,
          C.eval (List.ofFn x) = Bool.true ↔
            ∃ (x4 : Fin 13) (x5 : Fin 13),
              (x4 = x5 ∨ x4 = x5 + 1 ∨ x4 = x5 + 3 ∨ x4 = x5 + 9) ∧
                x4 ≠ 0 ∧ x (Fin.castAdd 13 x4) = Bool.true ∧
                  x (Fin.natAdd 13 x5) = Bool.true) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size) →
    (∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ x : Fin 26 → Bool,
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x =
          decide (∃ (x4 : Fin 13) (x5 : Fin 13),
            (x4 = x5 ∨ x4 = x5 + 1 ∨ x4 = x5 + 3 ∨ x4 = x5 + 9) ∧
              x4 ≠ 0 ∧ x (Fin.castAdd 13 x4) = true ∧ x (Fin.natAdd 13 x5) = true)) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        59 ≤ C.size) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 26 x1 →
      (∀ (x3 : Fin 26 → Bool),
        x1.eval (List.ofFn x3) = Bool.true ↔
          ∃ (x4 : Fin 13) (x5 : Fin 13),
            (x4 = x5 ∨ x4 = x5 + 1 ∨ x4 = x5 + 3 ∨ x4 = x5 + 9) ∧
              x4 ≠ 0 ∧ x3 (Fin.castAdd 13 x4) = Bool.true ∧ x3 (Fin.natAdd 13 x5) = Bool.true) →
      59 ≤ x1.size := by
  intro hGraph hNormalize hBound C hAO hEval
  rcases hGraph with ⟨G, hdec, hG⟩
  letI := hdec
  obtain ⟨D, hLeast, hTop, hSize⟩ := hNormalize G hG C hAO hEval
  have hD := hBound G hG D hLeast hTop
  omega
