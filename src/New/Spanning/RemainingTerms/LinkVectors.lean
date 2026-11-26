import New.Spanning.RemainingTerms.Data
import New.Spanning.Unfolding.TermStructure

/-!
# The vectors `z⁺` and `Υ_γ⁻¹ z⁺`

Let `γ` be an element of the unitary group, with the link isometry `Υ_γ` of the positive space
`X₀ ⊥ E z⁺`. Let `z` be the last vector of the frame and let `A` be spanned by the others.

* `New.Filling.linkVectors_mulVec_eq_zero_iff`: the orthogonal complement of `z⁺` and `Υ_γ⁻¹ z⁺`
  is `X₀^γ = X₀ ∩ Υ_γ⁻¹ X₀`.
* `New.Filling.gram_linkVectors`, `New.Filling.HasCellRank.norm_det_gram_linkVectors`: the Gram
  matrix of `z⁺` and `Υ_γ⁻¹ z⁺`, and the modulus of its determinant at each infinite place.
* `New.Filling.linkVectorPairs`: the negatives of the two vectors, as pairs in the graph of `Υ_γ`;
  there they represent the products with `z` and `γ z`
  (`New.Filling.linkVectorPairs_mul_linkMetric_mul`).

Notions from other files:
* `S.G E`: the unitary group of the form `S.ratGram` on the space with the basis `e₁, …, e_ϱ`, a
  basis of `X₀`, `z`, `e*₁, …, e*_ϱ`; the frame is `(e₁, …, e_ϱ, z)`.
* `S.positiveGram`: the Gram matrix of `X₀ ⊥ E z⁺`, where `z⁺` has the norm `N = S.N`.
* `linkIsometry γ`: the isometry `Υ_γ` of `X₀ ⊥ E z⁺`.
* `S.HasCellRank j γ`: the term `γ` has the cell rank `j`, the order of a distinguished leading
  minor of the products of the frame with its image under `γ`.
-/

noncomputable section

open Matrix Sum NumberField

namespace New.Filling

variable
  {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} {γ : S.G E} {j : Fin (𝔰.ϱ + 2)}

/--
The two vectors `z⁺` and `Υ_γ⁻¹ z⁺` of the positive space `X₀ ⊥ E z⁺`, as columns. Here
`Υ_γ = linkIsometry γ` is the link isometry of `γ`, and `inr ()` is the index of `z⁺`.
-/
def linkVectors (γ : S.G E) : Matrix 𝔰.MiddleIndex (Fin 2) E :=
  (of ![Pi.single (inr ()) 1, (linkIsometry γ).symm (Pi.single (inr ()) 1)])ᵀ

/--
The products of a vector `a` of `X₀ ⊥ E z⁺` with `z⁺` and `Υ_γ⁻¹ z⁺` are `N` times the
`z⁺`-coordinates of `a` and of `Υ_γ a`, where `Υ_γ` is the link isometry of `γ`.
-/
lemma linkVectors_mulVec (γ : S.G E) (a : 𝔰.MiddleIndex → E)
    : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ a
      = ![S.N * a (inr ()), S.N * linkIsometry γ a (inr ())] := by
  have h_single (b : 𝔰.MiddleIndex → E)
      : star (Pi.single (inr ()) 1 : 𝔰.MiddleIndex → E) ⬝ᵥ S.positiveGram *ᵥ b
        = S.N * b (inr ()) := by
    rw [dotProduct_positiveGram_mulVec_eq_sum_add]
    simp
  rw [← mulVec_mulVec]
  funext i
  fin_cases i
  · exact h_single a
  · change star ((linkIsometry γ).symm (Pi.single (inr ()) 1)) ⬝ᵥ S.positiveGram *ᵥ a
      = S.N * linkIsometry γ a (inr ())
    rw [← dotProduct_positiveGram_mulVec_linkIsometry γ, LinearEquiv.apply_symm_apply, h_single]

/--
The vectors `a` orthogonal, for `S.positiveGram`, to `z⁺` and `Υ_γ⁻¹ z⁺` in `X₀ ⊥ E z⁺` are
exactly the image under `inclPositive E 𝔰` of `X₀^γ = X₀ ∩ Υ_γ⁻¹ X₀` (`linkedX₀ γ`).
-/
theorem linkVectors_mulVec_eq_zero_iff (γ : S.G E) (a : 𝔰.MiddleIndex → E)
    : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ a = 0 ↔ a ∈ (linkedX₀ γ).map (inclPositive E 𝔰) := by
  have h_coords
      : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ a = 0
        ↔ a (inr ()) = 0 ∧ linkIsometry γ a (inr ()) = 0 := by
    simp [linkVectors_mulVec, S.N_prime.ne_zero]
  rw [h_coords, ← mem_range_inclPositive]
  constructor
  · rintro ⟨⟨v, rfl⟩, h_link⟩
    exact ⟨v, mem_linkedX₀.2 h_link, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, mem_linkedX₀.1 hv⟩

/--
A vector `y` is orthogonal to the frame `(γ e₁, …, γ e_ϱ, γ z)` if and only if the coordinates
of `γ⁻¹ y` at the dual basis vectors `e*_a` and at `z` vanish.
-/
lemma frameImage_conjTranspose_mulVec_eq_zero_iff (γ : S.G E) (y : 𝔰.BesselIndex → E)
    : ((frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram) *ᵥ y = 0
      ↔ (∀ a : Fin 𝔰.ϱ,
          ((↑(γ⁻¹ : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ y) (eStar a) = 0)
        ∧ ((↑(γ⁻¹ : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ y) 𝔰.z = 0 := by
  set x : 𝔰.BesselIndex → E := (↑(γ⁻¹ : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ y
    with hx
  have h_move
      : ((frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram) *ᵥ y
        = (S.ratGram *ᵥ x) ∘ 𝔰.besselFrame := by
    rw [hx, mulVec_mulVec, U.form_mul_inv_eq γ]
    rfl
  have h_dual (a : Fin 𝔰.ϱ) : (S.ratGram *ᵥ x) (𝔰.besselFrame a.castSucc) = x (eStar a) := by
    simp [Shape.besselFrame]
  have h_z : (S.ratGram *ᵥ x) (𝔰.besselFrame (Fin.last 𝔰.ϱ)) = -(S.N * x 𝔰.z) := by
    rw [splitGram_mulVec]
    simp [Shape.besselFrame, Shape.middleGram, mulVec, dotProduct]
  rw [h_move, funext_iff, Fin.forall_fin_succ']
  simp only [Function.comp_apply, h_dual, h_z]
  simp [S.N_prime.ne_zero]

/--
Let `γ` have a cell rank `j` (`HasCellRank`): it is in the normal form
`NormOnePairOccursFrom j γ`, the leading minor of order `j` of the products of the frame with its
image under `γ` is not zero, and `j` is the top index `ϱ + 1` exactly if the discriminant
`𝗀 = S.termDisc γ` of these two frames is not zero. If `𝗀 = 0`, then `Υ_γ⁻¹ z⁺` is a multiple of
`z⁺`.
-/
theorem HasCellRank.exists_linkIsometry_symm_eq_smul
    (hγ : S.HasCellRank j γ) (h_disc : S.termDisc γ = 0)
    : ∃ μ : E, (linkIsometry γ).symm (Pi.single (inr ()) 1) = μ • Pi.single (inr ()) 1 := by
  -- Here `X₀^γ = X₀`, so the vector is orthogonal to `X₀`.
  set w : 𝔰.MiddleIndex → E := (linkIsometry γ).symm (Pi.single (inr ()) 1)
  have h_orth (v : 𝔰.κ → E) : star w ⬝ᵥ S.positiveGram *ᵥ (v ⊕ᵥ 0) = 0 := by
    have h_products : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ (v ⊕ᵥ 0) = 0 :=
      (linkVectors_mulVec_eq_zero_iff γ _).2 ⟨v, by simp [hγ.linkedX₀_eq_top h_disc], rfl⟩
    rw [← mulVec_mulVec] at h_products
    exact congrFun h_products 1
  use w (inr ())
  ext (i | i)
  · have h_coord : star w ⬝ᵥ S.positiveGram *ᵥ (Pi.single i 1 ⊕ᵥ 0) = star (w (inl i)) := by
      rw [dotProduct_positiveGram_mulVec_eq_sum_add]
      simp [Pi.single_apply]
    rw [h_orth, eq_comm, star_eq_zero] at h_coord
    simp [h_coord]
  · simp

/--
Let `γ` have the cell rank `j`: it is in the normal form `NormOnePairOccursFrom j γ`, the
leading minor `δ_j` of order `j` of the products of the frame with its image under `γ` is not zero,
and `j` is the top index exactly if the discriminant `𝗀` of these two frames is not zero. Then
`𝗀 = |δ_j|² (1 - |u|²)`, where `u` is the `z⁺`-coordinate of `Υ_γ⁻¹ z⁺`, `Υ_γ` is the link
isometry of `γ`, and `|x|²` means `x x̄`.
-/
lemma HasCellRank.termDisc_eq_mul_linkIsometry_symm (hγ : S.HasCellRank j γ)
    : S.termDisc γ
      = leadingMinor (S.frameProducts γ) j * star (leadingMinor (S.frameProducts γ) j)
        * (1
          - star ((linkIsometry γ).symm (Pi.single (inr ()) 1) (inr ()))
            * (linkIsometry γ).symm (Pi.single (inr ()) 1) (inr ())) := by
  set w : 𝔰.MiddleIndex → E := (linkIsometry γ).symm (Pi.single (inr ()) 1) with hw
  have hN : (S.N : E) ≠ 0 := Nat.cast_ne_zero.2 S.N_prime.ne_zero
  by_cases h_disc : S.termDisc γ = 0
  · -- The vector `w` is `μ z⁺` and has the norm of `z⁺`, so `|μ| = 1`.
    obtain ⟨μ, hμ⟩ : ∃ μ : E, w = μ • Pi.single (inr ()) 1 :=
      hγ.exists_linkIsometry_symm_eq_smul h_disc
    have h_norm : star w ⬝ᵥ S.positiveGram *ᵥ w = S.N := by
      rw [← dotProduct_positiveGram_mulVec_linkIsometry γ, hw, LinearEquiv.apply_symm_apply,
        dotProduct_positiveGram_mulVec_eq_sum_add]
      simp
    rw [hμ, dotProduct_positiveGram_mulVec_eq_sum_add] at h_norm
    simp [h_disc, hμ, show star μ * μ = 1 by simpa [hN] using h_norm]
  · -- Let `δ` be the determinant of the products and `δ'` the minor before it. The link sends
    -- `y₀ + δ' z⁺` to `-(δ / N) z⁺` for some `y₀` in `X₀`, so `w = -(N / δ) (y₀ + δ' z⁺)`.
    obtain rfl : j = ⊤ := Fin.eq_last_of_not_lt (not_lt.2 (hγ.lt_iff_termDisc_ne_zero.2 h_disc))
    have hδ : (S.frameProducts γ).det ≠ 0 := ((termDisc_pos_or_eq_zero γ).resolve_right h_disc).2
    obtain ⟨y, hy, hy_top⟩
        : ∃ y : Fin (𝔰.ϱ + 1) → E,
          S.frameProducts γ *ᵥ y = Pi.single 𝔰.top (S.frameProducts γ).det
            ∧ y 𝔰.top = leadingMinor (S.frameProducts γ) 𝔰.top.castSucc :=
      exists_mulVec_eq_single_det (S.frameProducts γ)
    have h_image
        : linkIsometry γ
            (-(S.N / (S.frameProducts γ).det)
              • (((frameImage γ *ᵥ y) ∘ 𝔰.indexX₀) ⊕ᵥ fun _ : Unit ↦ y 𝔰.top))
          = Pi.single (inr ()) 1 := by
      rw [map_smul, linkIsometry_frameImage_mulVec hy]
      ext (i | i) <;> simp [hN, hδ]
    have h_coord
        : w (inr ())
          = -(S.N / (S.frameProducts γ).det) * leadingMinor (S.frameProducts γ) 𝔰.top.castSucc := by
      rw [hw, ← h_image, LinearEquiv.symm_apply_apply, ← hy_top]
      rfl
    have h_minor : leadingMinor (S.frameProducts γ) ⊤ = (S.frameProducts γ).det := rfl
    rw [h_coord, h_minor, termDisc, frameDisc, star_mul', star_neg, star_div₀, star_natCast]
    field_simp [star_ne_zero.2 hδ]

/--
The Gram matrix of `z⁺` and `Υ_γ⁻¹ z⁺` for the form `S.positiveGram` of the positive space
`X₀ ⊥ E z⁺`. Both diagonal entries are `N = S.N`, the norm of `z⁺`. The entries off the diagonal are
`N u` (row 1, column 2) and `N ū` (row 2, column 1), where `u` is the `z⁺`-coordinate of
`Υ_γ⁻¹ z⁺`.
-/
lemma gram_linkVectors (γ : S.G E)
    : (linkVectors γ)ᴴ * S.positiveGram * linkVectors γ
      = !![(S.N : E), S.N * (linkIsometry γ).symm (Pi.single (inr ()) 1) (inr ());
          S.N * star ((linkIsometry γ).symm (Pi.single (inr ()) 1) (inr ())), S.N] := by
  set w : 𝔰.MiddleIndex → E := (linkIsometry γ).symm (Pi.single (inr ()) 1) with hw
  have h_first
      : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ Pi.single (inr ()) 1
        = ![(S.N : E), S.N * star (w (inr ()))] := by
    ext i
    fin_cases i <;> simp [linkVectors, positiveGram, Matrix.mul_apply, diagonal, hw, mul_comm]
  have h_second : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ w = ![S.N * w (inr ()), S.N] := by
    simp [linkVectors_mulVec, hw]
  ext i k
  fin_cases i <;> fin_cases k
  exacts [congrFun h_first 0, congrFun h_second 0, congrFun h_first 1, congrFun h_second 1]

/--
If `γ` has the cell rank `j` (`HasCellRank`), the Gram determinant of `z⁺` and `Υ_γ⁻¹ z⁺`,
times `|δ_j|²`, is `N² 𝗀`. Here `𝗀` is the discriminant of the frame and its image under `γ`, and
`δ_j` is the leading minor of order `j` of their products, which is not zero.
-/
lemma HasCellRank.det_gram_linkVectors_mul (hγ : S.HasCellRank j γ)
    : ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det
        * (leadingMinor (S.frameProducts γ) j * star (leadingMinor (S.frameProducts γ) j))
      = S.N ^ 2 * S.termDisc γ := by
  rw [gram_linkVectors, det_fin_two_of, hγ.termDisc_eq_mul_linkIsometry_symm]
  ring

/--
Let `γ` have the cell rank `j` (`HasCellRank`), so that the leading minor `δ_j` of order `j` of
the products of the frame with its image under `γ` is not zero, and let `𝗀` be the discriminant of
these two frames. At each infinite place `v` the Gram determinant of `z⁺` and `Υ_γ⁻¹ z⁺` has the
modulus `N² |𝗀|_v / |δ_j|_v²`. Here `|x|_v` is the modulus `‖Φ v x‖` under the complex embedding
chosen at `v`.
-/
lemma HasCellRank.norm_det_gram_linkVectors (hγ : S.HasCellRank j γ) (v : InfinitePlace E)
    : ‖Φ v ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det‖
      = S.N ^ 2 * ‖Φ v (S.termDisc γ)‖ / ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ ^ 2 := by
  have h_det
      : ‖Φ v (((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det *
          (leadingMinor (S.frameProducts γ) j * star (leadingMinor (S.frameProducts γ) j)))‖
        = ‖Φ v (S.N ^ 2 * S.termDisc γ)‖ := by
    rw [hγ.det_gram_linkVectors_mul]
  obtain ⟨-, h_minor : leadingMinor (S.frameProducts γ) j ≠ 0, -⟩ := hγ
  rw [eq_div_iff (by simpa using h_minor)]
  simpa [sq] using h_det

/-! ### The two vectors as pairs in the link -/

/--
The index in `linkVectors γ = (z⁺, Υ_γ⁻¹ z⁺)` of the vector that represents the product with
`z` on each half of a pair: `Υ_γ⁻¹ z⁺` for the first half and `z⁺` for the second half, on which
this is the product with `γ z` before the pair is formed.
-/
def zFormIndex : Unit ⊕ Unit → Fin 2 := Sum.elim (fun _ ↦ 1) fun _ ↦ 0

lemma zFormIndex_injective : zFormIndex.Injective := by decide

/--
The two pairs in the link of `γ` (the graph of `Υ_γ`) with the sources `-Υ_γ⁻¹ z⁺` (column
`inl ()`) and `-z⁺` (column `inr ()`).
-/
def linkVectorPairs (γ : S.G E) : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Unit ⊕ Unit) E :=
  (of fun a : Unit ⊕ Unit ↦ ((linkSourceEquiv γ).symm (- (linkVectors γ).col (zFormIndex a))).val)ᵀ

lemma col_linkVectorPairs_mem (γ : S.G E) (a : Unit ⊕ Unit) : (linkVectorPairs γ).col a ∈ link γ :=
  ((linkSourceEquiv γ).symm (- (linkVectors γ).col (zFormIndex a))).prop

lemma linkSource_col_linkVectorPairs (γ : S.G E) (a : Unit ⊕ Unit)
    : linkSource E 𝔰 ((linkVectorPairs γ).col a) = - (linkVectors γ).col (zFormIndex a) :=
  (linkSourceEquiv γ).apply_symm_apply _

/--
The link of `γ` (`link γ`) consists of the pairs of the classes of `t` and `γ⁻¹ t` modulo `A`,
for `t` orthogonal to `A` and `γ A`. Write such a pair as `p = (y₀ + λ' z, y₀' + λ z)`, so that `λ'`
is the `z`-coordinate of the first class and `λ` that of the second; its source `linkSource E 𝔰 p`
is `y₀ + λ z⁺`. The two columns of `linkVectorPairs γ` are the pairs with the sources `-Υ_γ⁻¹ z⁺`
(column `inl ()`) and `-z⁺` (column `inr ()`). The product of column `a` with `p`, for the form
`S.linkMetric` on pairs, is minus the product of column `zFormIndex a` of `linkVectors γ` with
`y₀ + λ z⁺`, for the form `S.positiveGram` of `X₀ ⊥ E z⁺`.
-/
lemma conjTranspose_linkVectorPairs_mul_mulVec_apply
    {p : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E} (hp : p ∈ link γ) (a : Unit ⊕ Unit)
    : (((linkVectorPairs γ)ᴴ * S.linkMetric) *ᵥ p) a
      = - (((linkVectors γ)ᴴ * S.positiveGram) *ᵥ linkSource E 𝔰 p) (zFormIndex a) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  change star ((linkVectorPairs γ).col a) ⬝ᵥ S.linkMetric *ᵥ p
    = -(star ((linkVectors γ).col (zFormIndex a)) ⬝ᵥ S.positiveGram *ᵥ linkSource E 𝔰 p)
  rw [linkMetric_form_of_mem_link (col_linkVectorPairs_mem γ a) hp, linkSource_col_linkVectorPairs,
    star_neg, neg_dotProduct]

omit [CMType E] in
lemma col_mem_of_colSpan_le
    {m σ : Type} [Fintype σ]
    {y : Matrix m σ E} {V : Submodule E (m → E)} (hy : colSpan y ≤ V)
    (a : σ)
    : y.col a ∈ V := by
  classical
  exact hy ⟨Pi.single a 1, y.mulVec_single_one a⟩

/--
Let the columns of `w` lie in the link of `γ`. Their products with the columns of
`linkVectorPairs γ` for `S.linkMetric` are the two rows `zRowBlockDiagonal (S.ratMiddle E)` applied
to them: the products with `z` on each half of a pair.
-/
lemma linkVectorPairs_mul_linkMetric_mul
    {σ : Type} [Fintype σ]
    {w : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) σ E} (hw : colSpan w ≤ link γ)
    : (linkVectorPairs γ)ᴴ * S.linkMetric * w = zRowBlockDiagonal (S.ratMiddle E) * w := by
  ext a i
  have h_mem : w.col i ∈ link γ := col_mem_of_colSpan_le hw i
  change (((linkVectorPairs γ)ᴴ * S.linkMetric) *ᵥ w.col i) a
    = (zRowBlockDiagonal (S.ratMiddle E) *ᵥ w.col i) a
  rw [conjTranspose_linkVectorPairs_mul_mulVec_apply h_mem, linkVectors_mulVec,
    linkIsometry_linkSource h_mem]
  cases a <;> simp [zFormIndex, linkSource, linkTarget, Shape.middleGram, mulVec, dotProduct]

/--
The Gram matrix of the two columns of `linkVectorPairs γ` for `S.linkMetric` equals the Gram
matrix of `Υ_γ⁻¹ z⁺` and `z⁺` for `S.positiveGram`: that is, the Gram matrix of the columns of
`linkVectors γ`, reindexed by `zFormIndex`.
-/
lemma gram_linkVectorPairs (γ : S.G E)
    : (linkVectorPairs γ)ᴴ * S.linkMetric * linkVectorPairs γ
      = ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).submatrix zFormIndex zFormIndex := by
  ext a b
  change (((linkVectorPairs γ)ᴴ * S.linkMetric) *ᵥ (linkVectorPairs γ).col b) a
    = (((linkVectors γ)ᴴ * S.positiveGram) *ᵥ (linkVectors γ).col (zFormIndex b)) (zFormIndex a)
  rw [conjTranspose_linkVectorPairs_mul_mulVec_apply (col_linkVectorPairs_mem γ b),
    linkSource_col_linkVectorPairs, mulVec_neg, Pi.neg_apply, neg_neg]

end New.Filling
