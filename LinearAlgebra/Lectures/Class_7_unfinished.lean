import Mathlib
/-!-/
open Matrix
open scoped BigOperators

theorem rref_unique
    {m n : ℕ}
    {R₁ R₂ : Matrix (Fin m) (Fin (n)) ℝ}
    (hr₁ : R₁.IsReducedRowEchelon)
    (hr₂ : R₂.IsReducedRowEchelon)
    (h : R₁.RowEquivalent R₂) :
    R₁ = R₂ := by
  by_contra
  unfold RowEquivalent at *
  unfold MulAction.orbit at *
  unfold Set.range at *
  obtain ⟨m₁, hm₁⟩ := h
  replace hm₁ : (m₁ : Matrix (Fin m) (Fin m) ℝ) * R₁ = R₂ := by simpa using hm₁
  have hker : (((m₁ : Matrix (Fin m) (Fin m) ℝ) * R₁).mulVecLin).ker =
      R₁.mulVecLin.ker := by
    ext v
    constructor
    · intro hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have hv' := congrArg
        (fun w : Fin m → ℝ => (↑(m₁⁻¹) : Matrix (Fin m) (Fin m) ℝ) *ᵥ w) hv
      have hv'' :
          (((↑(m₁⁻¹) : Matrix (Fin m) (Fin m) ℝ) * (↑m₁ : Matrix (Fin m) (Fin m) ℝ)) * R₁) *ᵥ v = 0 := by
        simpa [Matrix.mulVec_mulVec] using hv'
      have hunit :
          (↑(m₁⁻¹) : Matrix (Fin m) (Fin m) ℝ) * (↑m₁ : Matrix (Fin m) (Fin m) ℝ) = 1 := by
        exact m₁.inv_val
      rw [hunit] at hv''
      simpa using hv''
    · intro hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi

  let mneZero : NeZero m := i.neZero
  let nneZero : NeZero n := j.neZero

  have hj' : R₁.col j ≠ R₂.col j := by
    intro hcol
    apply hij
    exact congrFun hcol i

  let S : Finset (Fin n) :=
    Finset.univ.filter (fun j => R₁.col j ≠ R₂.col j)

  have hS : S.Nonempty := by
    refine ⟨j, ?_⟩
    simp [S, hj']

  let j₀ : Fin n := S.min' hS

  have hj₀_diff : R₁.col j₀ ≠ R₂.col j₀ := by
    have hj₀_mem : j₀ ∈ S := by
      simpa [j₀] using S.min'_mem hS
    simpa [S] using hj₀_mem

  have hbefore :
      ∀ k < j₀, R₁.col k = R₂.col k := by
    intro k hk
    by_contra hneq

    have hk_mem : k ∈ S := by
      simp [S, hneq]

    have hj₀_le_k : j₀ ≤ k := by
      simpa [j₀] using Finset.min'_le S k hk_mem

    exact (not_le_of_gt hk) hj₀_le_k

  have hiff : ∀ v : Fin n → ℝ, R₁ *ᵥ v = 0 ↔ R₂ *ᵥ v = 0 := by
    intro v
    have hv := SetLike.ext_iff.mp hker v
    rw [hm₁, LinearMap.mem_ker, LinearMap.mem_ker,
      Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hv
    exact hv.symm

  by_cases hj₀: j₀ = 0
  · have hdiff0 : R₁.col 0 ≠ R₂.col 0 := by simpa [hj₀] using hj₀_diff

    have hfirst : ∀ A : Matrix (Fin m) (Fin n) ℝ, A.IsReducedRowEchelon →
      A.col 0 = 0 ∨ A.col 0 = Pi.single (0 : Fin m) 1 := by
      sorry

    have hcases : (R₁.col 0 = 0 ∧ R₂.col 0 ≠ 0) ∨ (R₁.col 0 ≠ 0 ∧ R₂.col 0 = 0) := by
      have hsingle : (Pi.single (0 : Fin m) (1 : ℝ) : Fin m → ℝ) ≠ 0 := by
        simp
      rcases hfirst R₁ hr₁ with h1 | h1 <;> rcases hfirst R₂ hr₂ with h2 | h2
      · exact absurd (h1.trans h2.symm) hdiff0
      · left
        exact ⟨h1, h2 ▸ hsingle⟩
      · right
        exact ⟨h1 ▸ hsingle, h2⟩
      · exact absurd (h1.trans h2.symm) hdiff0

    /- next close the subgoal -/
    have case1 : R₁.col 0 = 0 ∧ R₂.col 0 ≠ 0 → False := by
      rintro ⟨h1, h2⟩
      have hRe : ∀ A : Matrix (Fin m) (Fin n) ℝ,
          A *ᵥ Pi.single (0 : Fin n) 1 = A.col 0 :=
        fun A => Matrix.mulVec_single_one A 0
      apply h2
      rw [← hRe] at h1 ⊢
      exact (hiff _).mp h1

    have case2 : R₁.col 0 ≠ 0 ∧ R₂.col 0 = 0 → False := by
      rintro ⟨h1, h2⟩
      have hRe : ∀ A : Matrix (Fin m) (Fin n) ℝ,
          A *ᵥ Pi.single (0 : Fin n) 1 = A.col 0 :=
        fun A => Matrix.mulVec_single_one A 0
      apply h1
      rw [← hRe] at h2 ⊢
      exact (hiff _).mpr h2

    exact hcases.elim case1 case2

  · -- j₀ > 0
    -- 只保留對 R₁、R₂ 對稱的假設，才能用 wlog 交換兩者
    clear_value j₀
    clear hj' hij hi hS S hker hm₁ m₁ this
    -- 不失一般性，設 R₁ 的第 j₀ 欄不是主元欄
    wlog hnp : ¬ ∃ i, R₁.IsLeadingEntry i j₀ generalizing R₁ R₂ with H
    · -- 兩矩陣的第 j₀ 欄不能同時是主元欄（否則都等於 e_{r+1}，與 hj₀_diff 矛盾）
      have hnp₂ : ¬ ∃ i, R₂.IsLeadingEntry i j₀ := by
        rintro ⟨i₂, h₂⟩
        obtain ⟨i₁, h₁⟩ := not_not.mp hnp
        -- 前 j₀-1 個共同欄中共有 r 個主元欄
        let r : ℕ :=
          (Finset.univ.filter fun k : Fin n => k < j₀ ∧ ∃ i, R₁.IsLeadingEntry i k).card
        -- 第 j₀ 欄是主元欄，所以 r < m，e_{r+1} 才是 ℝ^m 中的向量
        have hr_lt : r < m := by
          sorry
        -- e_{r+1}（Fin 從 0 數，所以下標是 r）
        let e : Fin m → ℝ := Pi.single (⟨r, hr_lt⟩ : Fin m) 1
        -- 由 RREF 的性質，R₁ 的第 j₀ 欄等於 e_{r+1}
        have hcol₁ : R₁.col j₀ = e := by
          sorry
        -- R₂ 同理（前 j₀-1 欄相同，所以主元欄個數也是 r）
        have hcol₂ : R₂.col j₀ = e := by
          sorry
        -- 與第 j₀ 欄不同矛盾
        exact hj₀_diff (hcol₁.trans hcol₂.symm)
      exact H hr₂ hr₁ (Ne.symm hj₀_diff) (fun k hk => (hbefore k hk).symm)
        (fun v => (hiff v).symm) hnp₂

    obtain ⟨a, ha⟩ : ∃ a : Fin n → ℝ,
        R₁.col j₀ = ∑ j ∈ Finset.Iio j₀, a j • R₁.col j := by
      sorry

    -- v = (-a₁, …, -a_{j₀-1}, 1, 0, …, 0)ᵀ
    let v : Fin n → ℝ := Pi.single j₀ 1 - ∑ j ∈ Finset.Iio j₀, a j • Pi.single j 1

    have hR₁v : R₁ *ᵥ v = 0 := by
      sorry

    have hR₂v_expand : R₂ *ᵥ v = R₂.col j₀ - ∑ j ∈ Finset.Iio j₀, a j • R₂.col j := by
      sorry

    have hsum : ∑ j ∈ Finset.Iio j₀, a j • R₂.col j = R₁.col j₀ := by
      sorry

    have hR₂v : R₂ *ᵥ v ≠ 0 := by
      sorry

    /- next close the subgoal -/
    exact hR₂v ((hiff v).mp hR₁v)
