import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepPath

theorem PEqualNP.Outside.L_meta_19401 :
    ∀ n : ℕ, 4 ≤ n →
      ¬ PEqualNP.Represents.RepSizeAtMost
        (fun (u : Fin n) (v : Fin n) =>
          decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨
            (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨
            (2 ≤ u.val ∧ v.val ≤ 2))) (2 * n - 1) := by
  intro n hn hsmall
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  let A : Fin n → Fin n → Bool := fun u v =>
    decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨
      (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨
      (2 ≤ u.val ∧ v.val ≤ 2))
  obtain ⟨C, hmono, hsize, hrep⟩ := hsmall
  change PEqualNP.Represents.Represents A C at hrep
  have h21 : A i2 i1 = true := by
    simp [A, i0, i1, i2]
  have h20 : A i2 i0 = true := by
    simp [A, i0, i1, i2]
  have h01 : A i0 i1 = true := by
    simp [A, i0, i1, i2]
  have h00 : A i0 i0 = false := by
    simp [A, i0, i1]
  have hrowmiss : ∃ w : Fin n, A i2 w = false := by
    refine ⟨i3, ?_⟩
    simp [A, i0, i1, i2, i3]
  have hcolmiss : ∃ u : Fin n, A u i1 = false := by
    refine ⟨i1, ?_⟩
    simp [A, i0, i1]
  have rows : ∀ a : Fin n, ∃ b : Fin n, A a b = true ∧
      ∃ a' : Fin n, A a' b = false := by
    intro a
    by_cases h0 : a.val = 0
    · refine ⟨i1, ?_, ⟨i1, ?_⟩⟩ <;> norm_num [A, i0, i1, i2, h0]
    · by_cases h1 : a.val = 1
      · refine ⟨i0, ?_, ⟨i0, ?_⟩⟩ <;> norm_num [A, i0, i1, i2, h0, h1]
      · have hge : 2 ≤ a.val := by omega
        refine ⟨i0, ?_, ⟨i0, ?_⟩⟩
        · norm_num [A, i0, i1, i2, h0, h1, hge]
        · norm_num [A, i0, i1, i2]
  have cols : ∀ b : Fin n, ∃ a : Fin n, A a b = true ∧
      ∃ b' : Fin n, A a b' = false := by
    intro b
    by_cases h0 : b.val = 0
    · refine ⟨i2, ?_, ⟨i3, ?_⟩⟩ <;> norm_num [A, i0, i1, i2, i3, h0]
    · by_cases h2 : b.val ≤ 2
      · have h12 : b.val = 1 ∨ b.val = 2 := by omega
        rcases h12 with h1 | h2'
        · refine ⟨i0, ?_, ⟨i0, ?_⟩⟩ <;> norm_num [A, i0, i1, i2, h1]
        · refine ⟨i0, ?_, ⟨i0, ?_⟩⟩ <;> norm_num [A, i0, i1, i2, h2']
      · have hgt : 2 < b.val := by omega
        refine ⟨i1, ?_, ⟨i1, ?_⟩⟩
        · simp [A, i0, i1, i2] <;> omega
        · norm_num [A, i0, i1, i2]
  have hpath := PEqualNP.MetaComplexity.RepPath.path n n (2 * n - 1) A
    i2 i0 i1 i0
    h21 h20 h01 h00 hrowmiss hcolmiss ⟨C, hmono, hsize, hrep⟩
  have hrows :
      (Finset.univ.filter (fun a : Fin n =>
        ∃ b : Fin n, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card = n := by
    have heq : Finset.univ.filter (fun a : Fin n =>
        ∃ b : Fin n, A a b = true ∧ ∃ a' : Fin n, A a' b = false) = Finset.univ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact rows a
    rw [heq]
    simp
  have hcols :
      (Finset.univ.filter (fun b : Fin n =>
        ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin n, A a b' = false)).card = n := by
    have heq : Finset.univ.filter (fun b : Fin n =>
        ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin n, A a b' = false) = Finset.univ := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact cols b
    rw [heq]
    simp
  rw [hrows, hcols] at hpath
  omega
