import New.Spanning.Unfolding.Climbing

/-!
# The finite groups `Ū`, `H̄` and `R̄`

The factor of `Ū = S.reducedImage besselU` at each chosen place `w` consists of the block
unitriangular matrices over `𝔽_w` (`mem_reducedImage_besselU`). Counting free entries gives the
order of `Ū` (`card_reducedImage_besselU`). Each element of `R̄ = S.reducedImage besselS` is a
product of elements of `Ū` and `H̄ = S.reducedImage besselH` (`mem_reducedImage_besselS`), and
these two meet in the identity, giving `|R̄| = |H̄| |Ū|` (`card_reducedImage_besselS`). The order of
`H̄` is the index of `S.principalLevel.comap S.inclHFin` in `S.latticeStabilizer.comap S.inclHFin`
(`relIndex_comap_principalLevel`).

Notions from other files:
* `unitriangular lev R`: the invertible matrices over `R` that agree with `1` at the entries
  `(i, j)` with `lev j ≤ lev i`; `BesselIndex.level` is the level function of the Bessel basis.
* `S : Filling E 𝔰`: the data of the filling theorem, among them the sets `S.chosenPlaces i`.
* `S.latticeStabilizer`: the elements of the finite adelic unitary group `S.GFin` that are
  invertible over the integral adeles `Ô E`; `S.reduction` reduces them modulo the chosen places.
* `S.reducedImage B`: the image of `B ⊓ S.latticeStabilizer` under `S.reduction`.
-/

noncomputable section

open Matrix Finset

namespace New

/--
A ring homomorphism maps the entries of the identity matrix to those of the identity matrix:
the entrywise form of `Matrix.map_one`.
-/
lemma map_matrix_one_apply
    {n R R' : Type*} [DecidableEq n] [CommRing R] [CommRing R'] (f : R →+* R') (i j : n)
    : f ((1 : Matrix n n R) i j) = (1 : Matrix n n R') i j :=
  congrFun₂ (Matrix.map_one f f.map_zero f.map_one) i j

section Unitriangular

variable {n α R : Type*} [Fintype n] [DecidableEq n] [LinearOrder α] [CommRing R] (lev : n → α)

/-- The free entries of a block unitriangular matrix: the pairs `(i, j)` with `lev i < lev j`. -/
abbrev FreeEntry (lev : n → α) : Type _ := {p : n × n // lev p.1 < lev p.2}

/--
A matrix that is block unitriangular for the level function `lev` (equal to `1` at the entries
`(i, j)` with `lev j ≤ lev i`) is the same as a choice of its free entries.
-/
def unitriangularEquiv (R : Type*) [CommRing R] : unitriangular lev R ≃ (FreeEntry lev → R) where
  toFun u p := (u : GL n R) p.val.1 p.val.2
  invFun a :=
    let Z : Matrix n n R :=
      of fun i j ↦ if h : lev i < lev j then a ⟨(i, j), h⟩ else (1 : Matrix n n R) i j
    have hZ : ∀ i j : n, lev j ≤ lev i → Z i j = (1 : Matrix n n R) i j := fun _ _ hij ↦
      dite_eq_right hij.not_gt
    have h_det : IsUnit Z.det := by simp [det_eq_one_of_unitriangular hZ]
    ⟨GeneralLinearGroup.mk'' Z h_det, hZ⟩
  left_inv u := by
    ext i j
    change (if lev i < lev j then (u : GL n R) i j else (1 : Matrix n n R) i j) = (u : GL n R) i j
    exact ite_eq_left_iff.2 fun hij ↦ (u.2 i j (not_lt.1 hij)).symm
  right_inv a := funext fun p ↦ dite_eq_left p.2

/--
The block unitriangular matrix with the free entries `a` has the entry `a (i, j)` at a pair
`(i, j)` with `lev i < lev j`.
-/
lemma unitriangularEquiv_symm_apply_of_lt (a : FreeEntry lev → R) {i j : n} (hij : lev i < lev j)
    : ((unitriangularEquiv lev R).symm a : GL n R) i j = a ⟨(i, j), hij⟩ :=
  dite_eq_left hij

/--
The number of matrices over a ring with `q` elements that are block unitriangular for the level
function `lev` is `q` to the power of the number of free entries.
-/
lemma card_unitriangular (R : Type*) [CommRing R]
    : Nat.card (unitriangular lev R) = Nat.card R ^ Nat.card (FreeEntry lev) :=
  (Nat.card_congr (unitriangularEquiv lev R)).trans Nat.card_fun

/--
Let `n` be the index type and `lev : n → α` a level function. Suppose every family `t` has a
common preimage `y` under the maps `f p : R → F p`. Then a family `s p` in `unitriangular lev (F p)`
lifts to one `u` in `unitriangular lev R` with `GeneralLinearGroup.map (f p) u = s p`.
-/
lemma exists_unitriangular_map_eq
    {ι : Type*} {F : ι → Type*} [∀ p : ι, CommRing (F p)]
    (f : ∀ p : ι, R →+* F p) (hf : ∀ t : ∀ p : ι, F p, ∃ y : R, ∀ p : ι, f p y = t p)
    (s : ∀ p : ι, GL n (F p)) (hs : ∀ p : ι, s p ∈ unitriangular lev (F p))
    : ∃ u ∈ unitriangular lev R, ∀ p : ι, GeneralLinearGroup.map (f p) u = s p := by
  -- Lift the free entries; the others are those of the identity matrix.
  choose lift h_lift using fun e : FreeEntry lev ↦ hf fun p ↦ s p e.val.1 e.val.2
  let u : unitriangular lev R := (unitriangularEquiv lev R).symm lift
  refine ⟨u, u.2, fun p ↦ GeneralLinearGroup.ext fun i j ↦ ?_⟩
  change f p ((u : GL n R) i j) = s p i j
  obtain h_free | h_fixed := lt_or_ge (lev i) (lev j)
  · rw [unitriangularEquiv_symm_apply_of_lt lev lift h_free, h_lift]
  · rw [u.2 i j h_fixed, hs p i j h_fixed, map_matrix_one_apply]

/--
The level function `BesselIndex.level` has the block sizes `1, …, 1, m, 1, …, 1`, with `ϱ` ones
on each side and `m` the cardinality of `μ`. It has `(2ϱ choose 2) + 2ϱ m` free entries.
-/
lemma card_freeEntry_level (ϱ : ℕ) (μ : Type) [Fintype μ]
    : Nat.card (FreeEntry (BesselIndex.level (ϱ := ϱ) (μ := μ)))
      = (2 * ϱ).choose 2 + 2 * ϱ * Fintype.card μ := by
  -- The row `i` has its free entries at the indices of higher level. Count them for `i` in each
  -- of the three blocks of indices, of level `< ϱ`, `= ϱ` and `> ϱ`.
  let row (i : SplitIndex ϱ μ) : ℕ :=
    ∑ j : SplitIndex ϱ μ, if BesselIndex.level i < BesselIndex.level j then 1 else 0
  have h_lt_high (b : Fin ϱ) {c : ℕ} (hc : c ≤ ϱ) : c < 2 * ϱ - b := by omega
  have h_low (a : Fin ϱ)
      : row (.inl a) = ∑ b : Fin ϱ, (if a < b then 1 else 0) + (Fintype.card μ + ϱ) := by
    simp [row, BesselIndex.level, h_lt_high, -sum_boole]
  have h_mid (x : μ) : row (.inr (.inl x)) = ϱ := by
    simp [row, BesselIndex.level, fun b : Fin ϱ ↦ b.isLt.le.not_gt, h_lt_high, -sum_boole]
  have h_high (a : Fin ϱ) : row (.inr (.inr a)) = ∑ b : Fin ϱ, if b < a then 1 else 0 := by
    have h_high_iff (b : Fin ϱ) : 2 * ϱ - a < 2 * ϱ - b ↔ b < a := by omega
    simp [row, BesselIndex.level, h_lt_high, lt_asymm, h_high_iff, -sum_boole]
  have h_pairs_lt : ∑ a : Fin ϱ, ∑ b : Fin ϱ, (if a < b then 1 else 0) = ϱ.choose 2 := by
    rw [← Fintype.sum_prod_type', ← card_filter, Fintype.card_product_filter_lt, Fintype.card_fin]
  have h_pairs_gt : ∑ a : Fin ϱ, ∑ b : Fin ϱ, (if b < a then 1 else 0) = ϱ.choose 2 :=
    sum_comm.trans h_pairs_lt
  have h_choose : (2 * ϱ).choose 2 = ϱ.choose 2 + ϱ * ϱ + ϱ.choose 2 := by
    simp [two_mul, Nat.add_choose_eq, Finset.Nat.antidiagonal_succ, add_assoc]
  calc
    _ = ∑ i : SplitIndex ϱ μ, row i := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter, Fintype.sum_prod_type]
    _ = ϱ.choose 2 + ϱ * (Fintype.card μ + ϱ) + Fintype.card μ * ϱ + ϱ.choose 2 := by
      simp [h_low, h_mid, h_high, sum_add_distrib, h_pairs_lt, h_pairs_gt, add_assoc, -sum_boole]
    _ = (2 * ϱ).choose 2 + 2 * ϱ * Fintype.card μ := by linarith [h_choose]

end Unitriangular

section Unitary

variable {n R : Type*} [Fintype n] [CommRing R] [StarRing R] [DecidableEq n]

/--
Let `J` be a hermitian matrix, `e` an idempotent with `e ē = 0`, and `u'` an inverse adjoint of
`u`, that is `uᴴ J u' = J`. The matrix that is `u` on the factor `e R`, `u'` on the factor `ē R`
and `1` on the remaining factor preserves `J`.
-/
lemma conjTranspose_one_add_smul_sub_one_mul_mul_eq
    {J u u' : Matrix n n R} {e : R}
    (hJ : Jᴴ = J) (he : e * e = e) (he_star : e * star e = 0) (h_adj : uᴴ * J * u' = J)
    : (1 + e • (u - 1) + star e • (u' - 1))ᴴ * J * (1 + e • (u - 1) + star e • (u' - 1)) = J := by
  have h_adj' : u'ᴴ * J * u = J := by simpa [hJ, mul_assoc] using congrArg conjTranspose h_adj
  have he' : star e * star e = star e := by rw [← star_mul, he]
  -- Expand; the terms with the factor `e ē` vanish.
  calc
    _ = J + e • (u'ᴴ * J * u - J) + star e • (uᴴ * J * u' - J) := by
      simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_sub, conjTranspose_one,
        star_star, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add,
        smul_sub, smul_smul, he, he', he_star, mul_comm (star e) e, one_mul, mul_one, zero_smul]
      abel
    _ = J := by simp [h_adj, h_adj']

/--
The split form `T.splitGram` (`ϱ` hyperbolic planes and a middle space with Gram matrix `T`)
has the entry zero at `(i, j)` unless the levels of `i` and `j` add up to `2ϱ`. The level is `a`
at the index `a` of the first block, `ϱ` on the middle block and `2ϱ - a` at the index `a` of the
last block.
-/
lemma splitGram_apply_eq_zero
    {A : Type} [CommRing A]
    {𝔰 : Shape} (T : 𝔰.Form A)
    {i j : 𝔰.BesselIndex} (h_level : BesselIndex.level i + BesselIndex.level j ≠ 2 * 𝔰.ϱ)
    : T.splitGram i j = 0 := by
  rcases i with a | a | a <;> rcases j with b | b | b
  case inl.inr.inr | inr.inr.inl =>
    have h_ne : a ≠ b := by
      simp only [BesselIndex.level, Sum.elim_inl, Sum.elim_inr] at h_level
      omega
    simp [splitGram, h_ne]
  case inr.inl.inr.inl => exact absurd (two_mul 𝔰.ϱ).symm h_level
  -- The six remaining blocks are zero.
  all_goals simp [splitGram]

/--
Let `T'` and `T` be arbitrary, and let `Z` be strictly block upper triangular: it vanishes at
the entries `(d, c)` where the level of `c` is at most that of `d`. Then so is
`T'.splitGram * Zᴴ * T.splitGram`: the transpose reverses the order of the levels, and the two Gram
matrices reverse it back.
-/
lemma splitGram_mul_conjTranspose_mul_splitGram_apply_eq_zero
    {A : Type} [CommRing A] [StarRing A]
    {𝔰 : Shape} (T' T : 𝔰.Form A)
    {Z : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A}
    (hZ : ∀ d c : 𝔰.BesselIndex, BesselIndex.level c ≤ BesselIndex.level d → Z d c = 0)
    {i j : 𝔰.BesselIndex} (hij : BesselIndex.level j ≤ BesselIndex.level i)
    : (T'.splitGram * Zᴴ * T.splitGram) i j = 0 := by
  simp only [Matrix.mul_apply, sum_mul]
  refine sum_eq_zero fun d _ ↦ sum_eq_zero fun c _ ↦ ?_
  by_cases h_left : BesselIndex.level i + BesselIndex.level c = 2 * 𝔰.ϱ
  · by_cases h_right : BesselIndex.level d + BesselIndex.level j = 2 * 𝔰.ϱ
    · rw [conjTranspose_apply, hZ d c (by omega), star_zero, mul_zero, zero_mul]
    · rw [splitGram_apply_eq_zero T h_right, mul_zero]
  · rw [splitGram_apply_eq_zero T' h_left, zero_mul, zero_mul]

/--
Let `J = T.splitGram` be the Gram matrix of `ϱ` hyperbolic planes and a middle space with
invertible Gram matrix `T`. A matrix `u` that is block unitriangular for `BesselIndex.level` has an
inverse adjoint `u'`, that is `uᴴ J u' = J`, which is again block unitriangular.
-/
lemma exists_invAdjoint_unitriangular
    {A : Type} [CommRing A] [StarRing A]
    {𝔰 : Shape} {T : 𝔰.Form A} (hT : IsUnit T)
    {u : GL 𝔰.BesselIndex A} (hu : u ∈ unitriangular BesselIndex.level A)
    : ∃ u' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A,
      u.valᴴ * T.splitGram * u' = T.splitGram
        ∧ ∀ i j : 𝔰.BesselIndex,
          BesselIndex.level j ≤ BesselIndex.level i
            → u' i j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i j := by
  -- Take `u' = J⁻¹ (u⁻¹)ᴴ J = 1 + J⁻¹ (u⁻¹ - 1)ᴴ J`, where `J⁻¹` is the split form of `T⁻¹`.
  obtain ⟨T', hT'⟩ : ∃ T' : 𝔰.Form A, T * T' = 1 := hT.exists_right_inv
  have h_inv : T.splitGram * T'.splitGram = 1 := splitGram_mul_splitGram_eq_one hT'
  refine ⟨1 + T'.splitGram * (u⁻¹.val - 1)ᴴ * T.splitGram, ?_, fun i j hij ↦ ?_⟩
  · calc
      _ = u.valᴴ * (1 + T.splitGram * T'.splitGram * (u⁻¹.val - 1)ᴴ) * T.splitGram := by
        noncomm_ring
      _ = (u⁻¹.val * u.val)ᴴ * T.splitGram := by simp [h_inv, -Units.inv_mul, -coe_units_inv]
      _ = T.splitGram := by rw [u.inv_mul, conjTranspose_one, one_mul]
  · rw [Matrix.add_apply, add_eq_left]
    exact splitGram_mul_conjTranspose_mul_splitGram_apply_eq_zero T' T
      (fun d c hdc ↦ sub_eq_zero.2 (inv_mem hu d c hdc))
      hij

end Unitary

namespace Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)

open scoped Classical in
/--
Let `P` be a set of chosen places of the filling data `S`. There is an idempotent `e` of the
ring `Ô E` of integral finite adeles with `e * star e = 0`, where `star` is complex conjugation.
Modulo the places of `P`, `e` reduces (`reduceAt`) to `1`, and modulo the other chosen places it
reduces to `0`. `star e` reduces to `0` modulo all the chosen places.
-/
lemma exists_idempotent_reduceAt_eq_ite (P : Set (Σ i : Fin 2, S.chosenPlaces i))
    : ∃ e : Ô E,
      e * e = e ∧ e * star e = 0
        ∧ ∀ p : Σ i : Fin 2, S.chosenPlaces i,
          reduceAt (p.2 : FinPlace E) e = (if p ∈ P then 1 else 0)
            ∧ reduceAt (p.2 : FinPlace E) (star e) = 0 := by
  let places : Set (FinPlace E) := (fun p ↦ (p.2 : FinPlace E)) '' P
  let e : Ô E := ⟨idem places, idem_mem_Ô places⟩
  have h_star_notMem
      : ∀ p : Σ i : Fin 2, S.chosenPlaces i, (p.2 : FinPlace E) ∉ star ⁻¹' places := by
    rintro ⟨i, w, hw⟩ ⟨⟨j, v, hv⟩, -, rfl : v = star w⟩
    exact S.star_notMem_chosenPlaces hw hv
  refine ⟨e, Subtype.ext (idem_mul_self places), ?_, fun p ↦ ⟨?_, ?_⟩⟩
  · refine Subtype.ext (IsDedekindDomain.FiniteAdeleRing.ext _ fun w ↦ ?_)
    change idem places w * star (idem places) w = 0
    by_cases hw : w ∈ places
    · obtain ⟨p, -, rfl⟩ := hw
      rw [star_idem, idem_of_notMem (h_star_notMem p), mul_zero]
    · rw [idem_of_notMem hw, zero_mul]
  · simp only [e, places, reduceAt_idem, S.chosenPlaces_injective.mem_set_image]
  · rw [show star e = ⟨idem (star ⁻¹' places), idem_mem_Ô _⟩ from Subtype.ext (star_idem places),
      reduceAt_idem, ite_eq_right (h_star_notMem p)]

open scoped Classical in
/--
Let `J = (S.latticeMiddle (Ô E)).splitGram` be the Gram matrix in the lattice basis of the
filling data `S`, let `u` and `u'` be matrices over the integral finite adeles with `uᴴ J u' = J`,
and let `P` be a set of chosen places. Some `k` in the stabiliser of the lattice agrees with `1` at
every entry where `u` and `u'` do, and its reduction is that of `u` modulo the places of `P` and `1`
modulo the other chosen places.
-/
lemma exists_reduction_eq_of_invAdjoint
    (P : Set (Σ i : Fin 2, S.chosenPlaces i))
    {u u' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E)}
    (h_adj : uᴴ * (S.latticeMiddle (Ô E)).splitGram * u' = (S.latticeMiddle (Ô E)).splitGram)
    : ∃ k : S.latticeStabilizer,
      (∀ a b : 𝔰.BesselIndex,
          u a b = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E)) a b
            → u' a b = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E)) a b
            → (k : GL 𝔰.BesselIndex (𝔸f E)) a b
              = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) a b)
        ∧ ∀ p : Σ i : Fin 2, S.chosenPlaces i,
          (S.reduction k p.1 p.2).val
            = if p ∈ P then u.map (reduceAt (p.2 : FinPlace E)) else 1 := by
  -- Glue `u` at the places of `P`, `u'` at their conjugates and `1` elsewhere.
  obtain ⟨e, he, he_star, h_red⟩ := S.exists_idempotent_reduceAt_eq_ite P
  let M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E) := 1 + e • (u - 1) + star e • (u' - 1)
  have hM : Mᴴ * (S.latticeMiddle (Ô E)).splitGram * M = (S.latticeMiddle (Ô E)).splitGram :=
    conjTranspose_one_add_smul_sub_one_mul_mul_eq Floors.IsHermitianUnit.conjTranspose_eq he he_star
      h_adj
  let g : (S.latticeMiddle (Ô E)).G := U.of Floors.IsHermitianUnit.isUnit M hM
  let k : S.GFin := U.map (Ô E).subtype coe_star_Ô (S.map_splitGram_latticeMiddle _) g
  refine ⟨⟨k, g, rfl⟩, fun a b hu hu' ↦ ?_, fun p ↦ ?_⟩
  · change (Ô E).subtype (M a b) = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) a b
    simp [M, hu, hu', map_matrix_one_apply]
  · change M.map (reduceAt (p.2 : FinPlace E)) = _
    ext a b
    split_ifs with hp <;> simp [M, h_red p, hp, map_matrix_one_apply]

/--
Let `k` lie in the stabiliser of the lattice (the integral points of the finite adelic unitary
group of the filling `S`). If `k` agrees with `1` at the entry `(a, b)`, so does its reduction at
every chosen place `w`.
-/
lemma reduction_apply_eq_one_apply
    {k : S.latticeStabilizer} {a b : 𝔰.BesselIndex}
    (hk : (k : GL 𝔰.BesselIndex (𝔸f E)) a b = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) a b)
    (i : Fin 2) (w : S.chosenPlaces i)
    : S.reduction k i w a b
      = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField (w : FinPlace E))) a b := by
  rw [reduction_apply_congr 1 i w hk, map_one, Pi.one_apply, Pi.one_apply, Units.val_one]

/--
Let `Ū = S.reducedImage besselU` be the reduction at the chosen places of the integral points of
the Bessel unipotent group. An element `s` of `S.ResidueGL`, the product of the general linear
groups over the residue fields at the chosen places, lies in `Ū` if and only if all its components
`s i w` are block upper unitriangular for `BesselIndex.level`.
-/
theorem mem_reducedImage_besselU {s : S.ResidueGL}
    : s ∈ S.reducedImage besselU
      ↔ ∀ (i : Fin 2) (w : S.chosenPlaces i),
        s i w ∈ unitriangular BesselIndex.level (ResField (w : FinPlace E)) := by
  refine ⟨?_, fun hs ↦ ?_⟩
  · rintro ⟨k, hk, rfl⟩ i w a b hab
    exact S.reduction_apply_eq_one_apply (hk a b hab) i w
  -- Lift the free entries to `Ô`, and complete the lift `u` by its inverse adjoint `u'`.
  have h_lift (t : ∀ p : Σ i : Fin 2, S.chosenPlaces i, ResField (p.2 : FinPlace E))
      : ∃ y : Ô E, ∀ p : Σ i : Fin 2, S.chosenPlaces i, reduceAt (p.2 : FinPlace E) y = t p :=
    -- Prescribe `t p` at both indices over `p`; the index `(p, false)` stands for `p` itself.
    (S.exists_reduceAboveM_eq fun x ↦ t x.1).imp fun y hy p ↦ hy (p, false)
  obtain ⟨u, hu, hu_red⟩ :=
    exists_unitriangular_map_eq BesselIndex.level _ h_lift _ fun p ↦ hs p.1 p.2
  obtain ⟨u', h_adj, hu'⟩ :=
    exists_invAdjoint_unitriangular (T := S.latticeMiddle (Ô E)) Floors.IsHermitianUnit.isUnit hu
  -- Some `k` agrees with `1` where `u` and `u'` do, and reduces as `u` does at all chosen places.
  obtain ⟨k, hk_one, hk_red⟩ := S.exists_reduction_eq_of_invAdjoint Set.univ h_adj
  refine ⟨k, fun a b hab ↦ hk_one a b (hu a b hab) (hu' a b hab), funext₂ fun i w ↦ Units.ext ?_⟩
  calc
    _ = u.val.map (reduceAt (w : FinPlace E)) := by rw [hk_red ⟨i, w⟩, ite_eq_left (Set.mem_univ _)]
    _ = (s i w).val := congrArg Units.val (hu_red ⟨i, w⟩)

/--
Let the shape `𝔰` have `ϱ = 𝔰.ϱ` hyperbolic planes and a summand `X₀` of rank `k = 𝔰.k`. The
function `BesselIndex.level` cuts the basis indices `𝔰.BesselIndex` into blocks of sizes
`1, …, 1, k + 1, 1, …, 1`, with `ϱ` ones on each side. There are `ϱ (2k + 2ϱ + 1)` free entries, the
positions `(i, j)` above the block diagonal.
-/
lemma card_freeEntry_besselIndex (𝔰 : Shape)
    : Nat.card (FreeEntry (BesselIndex.level : 𝔰.BesselIndex → ℕ))
      = 𝔰.ϱ * (2 * 𝔰.k + 2 * 𝔰.ϱ + 1) := by
  have h_choose : (2 * 𝔰.ϱ).choose 2 = 𝔰.ϱ * (2 * 𝔰.ϱ - 1) := by
    rw [Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  calc
    Nat.card (FreeEntry (BesselIndex.level : 𝔰.BesselIndex → ℕ))
        = (2 * 𝔰.ϱ).choose 2 + 2 * 𝔰.ϱ * (𝔰.k + 1) := by
      rw [card_freeEntry_level, show Fintype.card 𝔰.MiddleIndex = 𝔰.k + 1 by simp]
    _ = 𝔰.ϱ * (2 * 𝔰.ϱ - 1 + 2 * (𝔰.k + 1)) := by
      rw [h_choose]
      ring
    _ = 𝔰.ϱ * (2 * 𝔰.k + 2 * 𝔰.ϱ + 1) := by
      obtain h_zero | h_pos := Nat.eq_zero_or_pos 𝔰.ϱ
      · simp [h_zero]
      · rw [show 2 * 𝔰.ϱ - 1 + 2 * (𝔰.k + 1) = 2 * 𝔰.k + 2 * 𝔰.ϱ + 1 by omega]

/--
The order of `Ū = S.reducedImage besselU`, the reduction of the integral points of the Bessel
unipotent group, is `S.unipotentOrder = M ^ (f ϱ (2k + 2ϱ + 1))`. Here `M` is the product of the two
level primes, `f` the number of infinite places of `E`, `k` the dimension of `X₀` and `ϱ` the number
of hyperbolic planes.
-/
theorem card_reducedImage_besselU : Nat.card (S.reducedImage besselU) = S.unipotentOrder := by
  let d : ℕ := 𝔰.ϱ * (2 * 𝔰.k + 2 * 𝔰.ϱ + 1)
  let equivPi
      : S.reducedImage besselU
        ≃ ∀ (i : Fin 2) (w : S.chosenPlaces i),
          unitriangular (BesselIndex.level : 𝔰.BesselIndex → ℕ) (ResField (w : FinPlace E)) := {
    toFun s i w := ⟨(s : S.ResidueGL) i w, S.mem_reducedImage_besselU.1 s.2 i w⟩
    invFun t := ⟨fun i w ↦ t i w, S.mem_reducedImage_besselU.2 fun i w ↦ (t i w).2⟩
  }
  calc
    Nat.card (S.reducedImage besselU)
        = ∏ i : Fin 2, ∏ w : S.chosenPlaces i, Nat.card
            (unitriangular (BesselIndex.level : 𝔰.BesselIndex → ℕ) (ResField (w : FinPlace E))) :=
      by simp only [Nat.card_congr equivPi, Nat.card_pi]
    _ = ∏ i : Fin 2, ∏ _w : S.chosenPlaces i, S.levelPrime i ^ d := by
      simp only [card_unitriangular, card_freeEntry_besselIndex, card_resField_eq_levelPrime, d]
    _ = (S.levelPrime 0 * S.levelPrime 1) ^ (numInfPlaces E * d) := by
      simp [S.card_chosenPlaces, mul_pow, ← pow_mul, mul_comm d]
    _ = S.unipotentOrder := rfl

/--
If the image `S.inclHFin k` of an element `k` of the unitary group of `X₀` preserves the
lattice, then its reduction lies in `H̄ = S.reducedImage besselH`.
-/
lemma reduction_inclHFin_mem_reducedImage_besselH
    {k : Gf E 𝔰.κ} (hk : S.inclHFin k ∈ S.latticeStabilizer)
    : S.reduction ⟨S.inclHFin k, hk⟩ ∈ S.reducedImage besselH :=
  ⟨⟨S.inclHFin k, hk⟩, inclHFin_mem_besselH k, rfl⟩

/--
An element of the stabiliser of the lattice lies in the principal congruence subgroup
`S.principalLevel` if and only if it reduces to `1` at all chosen places.
-/
lemma coe_mem_principalLevel_iff_reduction_eq_one {k : S.latticeStabilizer}
    : (k : S.GFin) ∈ S.principalLevel ↔ S.reduction k = 1 :=
  Subgroup.mem_map_iff_mem S.latticeStabilizer.subtype_injective

/--
The finite adelic points `k` of the unitary group of `X₀` with `S.inclHFin k` in
`S.principalLevel` (the principal congruence subgroup) have index `|H̄|` among those with
`S.inclHFin k` in `S.latticeStabilizer`.
-/
theorem relIndex_comap_principalLevel
    : (S.principalLevel.comap S.inclHFin).relIndex (S.latticeStabilizer.comap S.inclHFin)
      = Nat.card (S.reducedImage besselH) := by
  -- The subgroup is the kernel of the reduction, whose image is `H̄`.
  let reduce : S.latticeStabilizer.comap S.inclHFin →* S.ResidueGL :=
    S.reduction.comp (S.inclHFin.subgroupComap S.latticeStabilizer)
  have h_ker
      : (S.principalLevel.comap S.inclHFin).subgroupOf (S.latticeStabilizer.comap S.inclHFin)
        = reduce.ker :=
    Subgroup.ext fun k ↦ S.coe_mem_principalLevel_iff_reduction_eq_one (k := ⟨S.inclHFin k, k.2⟩)
  have h_range : reduce.range = S.reducedImage besselH := by
    refine le_antisymm ?_ ?_
    · rintro s ⟨k, rfl⟩
      exact S.reduction_inclHFin_mem_reducedImage_besselH k.2
    · rintro s ⟨⟨x, hx⟩, hx_mem, rfl⟩
      obtain ⟨k, rfl⟩ : x ∈ S.inclHFin.range := range_inclHFin.ge hx_mem
      exact ⟨⟨k, hx⟩, rfl⟩
  rw [Subgroup.relIndex, h_ker, Subgroup.index_ker, h_range]

/--
The reductions `Ū` and `H̄` of the integral points of `besselU` and `besselH` at the chosen
places meet in the identity only.
-/
lemma disjoint_reducedImage_besselU_besselH
    : Disjoint (S.reducedImage besselU) (S.reducedImage besselH) := by
  refine Subgroup.disjoint_def.2 ?_
  rintro s ⟨u, hu, h_red⟩ ⟨h, hh, rfl⟩
  -- The element `u⁻¹ h` is congruent to `1`, hence so is its factor `h`.
  have h_prod : (u⁻¹ * h : S.GFin) ∈ S.principalLevel :=
    S.coe_mem_principalLevel_iff_reduction_eq_one.2 (show S.reduction (u⁻¹ * h) = 1 by simp [h_red])
  refine S.coe_mem_principalLevel_iff_reduction_eq_one.1 ?_
  rw [principalLevel_eq_unitaryLevel] at h_prod ⊢
  exact mem_unitaryLevel_of_besselU_mul (inv_mem hu) hh h_prod

/--
Let `S : Filling E 𝔰`. In `S.ResidueGL`, the matrix groups over the residue fields at the chosen
places of `S`, the reduction `R̄` of the integral points of `besselS` is the set of products `u * h`
with `u` in `Ū` and `h` in `H̄`.
-/
lemma mem_reducedImage_besselS {s : S.ResidueGL}
    : s ∈ S.reducedImage besselS
      ↔ ∃ u ∈ S.reducedImage besselU, ∃ h ∈ S.reducedImage besselH, s = u * h := by
  constructor
  · -- If `u h` is integral then so is `h` (`unitaryLevel (Ô E) 1` is the group of the integral
    -- points), hence also `u`.
    rintro ⟨⟨x, h_int⟩, h_mem, rfl⟩
    obtain ⟨u, hu, h, hh, rfl⟩ := mem_besselS.1 h_mem
    have hh_int : h ∈ S.latticeStabilizer :=
      unitaryLevel_one.le (mem_unitaryLevel_of_besselU_mul hu hh (unitaryLevel_one.ge h_int))
    have hu_int : u ∈ S.latticeStabilizer := (mul_mem_cancel_right hh_int).1 h_int
    exact ⟨
      S.reduction ⟨u, hu_int⟩,
      ⟨⟨u, hu_int⟩, hu, rfl⟩,
      S.reduction ⟨h, hh_int⟩,
      ⟨⟨h, hh_int⟩, hh, rfl⟩,
      S.reduction.map_mul ⟨u, hu_int⟩ ⟨h, hh_int⟩
    ⟩
  · rintro ⟨u', ⟨u, hu, rfl⟩, h', ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨u * h, mem_besselS.2 ⟨u, hu, h, hh, rfl⟩, S.reduction.map_mul u h⟩

/--
Let `Ū`, `H̄`, `R̄` be the reductions of `besselU`, `besselH` (the fixer of the basis vectors
outside `X₀`) and `besselS`. Then `|R̄| = |H̄| |Ū|`, where `|Ū| = S.unipotentOrder`.
-/
theorem card_reducedImage_besselS
    : Nat.card (S.reducedImage besselS) = Nat.card (S.reducedImage besselH) * S.unipotentOrder := by
  -- Multiplication is a bijection from `Ū × H̄` onto `R̄`.
  let mul (p : S.reducedImage besselU × S.reducedImage besselH) : S.reducedImage besselS :=
    ⟨p.1 * p.2, S.mem_reducedImage_besselS.2 ⟨p.1, p.1.prop, p.2, p.2.prop, rfl⟩⟩
  have h_bij : Function.Bijective mul := by
    refine ⟨
      fun p q hpq ↦
        Subgroup.mul_injective_of_disjoint S.disjoint_reducedImage_besselU_besselH
          (congrArg Subtype.val hpq),
      ?_
    ⟩
    rintro ⟨s, hs⟩
    obtain ⟨u, hu, h, hh, rfl⟩ := S.mem_reducedImage_besselS.1 hs
    exact ⟨(⟨u, hu⟩, ⟨h, hh⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective mul h_bij, Nat.card_prod, card_reducedImage_besselU, mul_comm]

end Filling

end New

end
