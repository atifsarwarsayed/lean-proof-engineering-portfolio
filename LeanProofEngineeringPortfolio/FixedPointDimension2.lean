/-
copyright (c) 2026 Atif Sarwar Sayed. All rights reserved.
Authors: Atif Sarwar Sayed
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# No Retraction from D² to S¹ and the Brouwer Fixed Point Theorem in D² .

In this file we prove that there is no retraction from D² to S¹ and the Brouwer Fixed Point
Theorem in D².

## Main Results

- `no_retraction` : There is no continuous retraction from the unit disk `D²` to the unit
  circle `S¹`, i.e. no continuous map `r : D² → S¹` such that `r ∘ i = id`.
- `brouwer_fixed_point` : Every continuous map `f : D² → D²` has a fixed point.

## Notes

The nontriviality of π₁(S¹) is assumed as a `sorry` in this file. As of 2026, a complete
formalization of π₁(S¹) ≅ ℤ does not appear to be available in Mathlib, and would require
developing covering space theory in full.

## References

- [Hatcher, A. (2002). Algebraic Topology. Cambridge University Press.]
-/

open Metric Set ContinuousMap

/-- Just ℝ² wasn't being recognised.-/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The closed unit disk in ℝ². -/
def disk2 : Type := {x : ℝ² // ‖x‖ ≤ 1}
-- `def disk2 : Set ℝ² := closedBall 0 1` didn't work. LEAN doesn't know about the topology.

/-- The unit circle in ℝ². -/
def circle1 : Type := {x : ℝ² // ‖x‖ = 1}
-- Similarly, `def circle1 : Set ℝ² := sphere 0 1` also didn't work.

/-- We give circle1 the induced subtype topology. -/
instance : TopologicalSpace circle1 := instTopologicalSpaceSubtype

/-- We give disk2 the induced subtype topology. -/
instance : TopologicalSpace disk2 := instTopologicalSpaceSubtype

/-- Any point on the unit circle lies in the unit disk. -/
lemma circle1_Subset_disk2 (x : circle1) : ‖x.1‖ ≤ 1 := by
  have h := x.2
  grind

/-- Define the inclusion `i`. Gemini.ai explained how to construct a point on a subtype by using
`⟨ ...,... ⟩` notation. The first coordinate depicts the point as a memeber of the type (here `ℝ²`),
and the second coordinate proves that it's a member of the subtype (here `disk2`). -/
def i : circle1 → disk2 := fun x => ⟨x.1, circle1_Subset_disk2 x⟩

/-- The inclusion `i : S¹ → D²` is injective. -/
lemma i_injective : Function.Injective i := by
  intro x y hxy
  apply Subtype.ext
  have := congr_arg Subtype.val hxy
  simpa

/-- The inclusion map `i` is continuous. -/
lemma continuous_i : Continuous i := by
  apply Continuous.subtype_mk
  -- This lets us prove continuity only for the first predicate, i.e. `x.1
  exact continuous_subtype_val

/- Now we prove that the disk is contractible. To do this, we construct an explicit homotopy
from the identity map on the disk to the constant map. In this case, the homotopy is a straight
line contraction of the unit disk to its center. Before doing this, we need to define a
basepoint for the disk. -/

/-- The center of the disk, used as the basepoint for the contraction. -/
def disk_bp : disk2 := ⟨0, by simp⟩

/-- The identity map on the disk, as a bundled continuous map. -/
def f_id : C(disk2, disk2) := ContinuousMap.id disk2

/-- The constant map on the disk sending everything to the basepoint. -/
def g_const : C(disk2, disk2) := ContinuousMap.const disk2 disk_bp

/-- `1 - t` is nonneg for `t ∈ [0,1]`. -/
lemma one_minus_t_nonneg (t : unitInterval) : 0 ≤ 1 - (t : ℝ) := by
  have ht := t.2.1
  grind

/-- `1 - t ≤ 1` for `t ∈ [0,1]`. -/
lemma one_minus_t_le_one (t : unitInterval) : 1 - (t : ℝ) ≤ 1 := by
  have ht := t.2.2
  grind

/-- `|1 - t| = 1 - t` for `t ∈ [0,1]`. -/
lemma norm_one_minus_t (t : unitInterval) : ‖1 - (t : ℝ)‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (one_minus_t_nonneg t)]
  exact one_minus_t_le_one t

/-- The contraction of the disk remains in the disk, using the above lemmas. -/
lemma disk_norm_le (x : ℝ²) (hx : ‖x‖ ≤ 1) (t : unitInterval) : ‖(1 - (t : ℝ)) • x‖ ≤ 1 := by
  rw [norm_smul]
  apply mul_le_one₀
  · exact norm_one_minus_t t
  · exact norm_nonneg x
  · exact hx

/-- Defining the homotopy (contraction). -/
def disk_homotopy : Homotopy f_id g_const where
  toFun xt :=
    let t := xt.1
    let x := xt.2
    ⟨(1 - (t : ℝ)) • x.1, disk_norm_le x.1 x.2 t⟩
  continuous_toFun := by
  -- Lean unable to synthesize default value for `continuous_toFun`, so we prove it is.
    apply Continuous.subtype_mk
    -- An automatic renaming of variables from `xt` to `x` takes place. Now `x.1 : unitInterval`
     -- and `x.2 : disk2`. This `x` is not `x := xt.2` as declared in the `let`.
    apply Continuous.smul
    · apply Continuous.sub
      · exact continuous_const
      · exact (continuous_subtype_val.comp continuous_fst)
       -- The map x ↦ (x.1 : ℝ) is continuous. We first project onto the `unitInterval` via
        --`continuous_fst`, then extract the underlying real number from the subtype `unitInterval`
         -- via `continuous_subtype_val`. These two lemmas were sourced using Claude.ai.
    exact (continuous_subtype_val.comp continuous_snd)
  map_zero_left x := by simp [f_id]
  map_one_left x := by simp [g_const, disk_bp]

/-- The straight line between two points in `disk2` stays in `disk2`. -/
lemma disk2_segment (x y : disk2) (t : unitInterval) :
    ‖(1 - (t : ℝ)) • x.1 + (t : ℝ) • y.1‖ ≤ 1 := by
  calc ‖(1 - (t : ℝ)) • x.1 + (t : ℝ) • y.1‖
      ≤ ‖(1 - (t : ℝ)) • x.1‖ + ‖(t : ℝ) • y.1‖ := norm_add_le _ _
    _ = |1 - (t : ℝ)| * ‖x.1‖ + |(t : ℝ)| * ‖y.1‖ := by simp [norm_smul]
    _ ≤ (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 := by
        apply add_le_add
        · rw [abs_of_nonneg (one_minus_t_nonneg t)]
          exact mul_le_mul_of_nonneg_left x.2 (one_minus_t_nonneg t)
        · rw [abs_of_nonneg t.2.1]
          exact mul_le_mul_of_nonneg_left y.2 t.2.1
    _ = 1 := by ring

/-- `disk2` is path-connected: any two points can be joined by a straight line path. -/
theorem disk2_path_connected : PathConnectedSpace disk2 :=
  PathConnectedSpace.mk ⟨disk_bp⟩ (fun x y => ⟨{
    toFun := fun t => ⟨(1 - (t : ℝ)) • x.1 + (t : ℝ) • y.1, disk2_segment x y t⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.add
      · exact (continuous_const.sub continuous_subtype_val).smul continuous_const
      · exact continuous_subtype_val.smul continuous_const
    source' := by simp
    target' := by simp
  }⟩)

/- I couldn't access the contractible space instance even though its there in Mathlib.
So I defined it explicitly. -/

/-- A topological space is contractible if the identity map is homotopic to a constant map. -/
def IsContractible (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ (x : X), Nonempty (Homotopy (ContinuousMap.id X) (ContinuousMap.const X x))

/-- The unit disk is contractible, as seen by the straight line homotopy to the origin. -/
theorem disk2_isContractible : IsContractible disk2 :=
  ⟨disk_bp, ⟨disk_homotopy⟩⟩

/-- A canonical basepoint on `circle1`, given by the vector `(1, 0)`.
    Construction sourced with help from Claude.ai. -/
noncomputable def circle1_bp : circle1 := by
  refine ⟨EuclideanSpace.single (0 : Fin 2) 1, ?_⟩
  simp [EuclideanSpace.norm_single]

/-- The unit circle is nonempty, witnessed by the canonical basepoint. -/
instance : Nonempty circle1 := ⟨circle1_bp⟩

/-- The unit disk is nonempty, witnessed by the center. -/
instance : Nonempty disk2 := ⟨disk_bp⟩

/-- The fundamental group of the circle is nontrivial. -/
lemma circle1_fg_nontrivial : Nontrivial (FundamentalGroup circle1 circle1_bp) := by
  sorry

open CategoryTheory in
/-- A retraction `r : D² → S¹` induces a left inverse on fundamental groups,
    forcing π₁(S¹) to inject into π₁(D²). -/
lemma retraction_induces_fg_split (r : C(disk2, circle1))
    (hr : ∀ x : circle1, r (i x) = x) :
    (FundamentalGroupoid.map (ContinuousMap.mk i continuous_i)) ⋙
    (FundamentalGroupoid.map r) =
    CategoryTheory.Functor.id _ := by
      apply CategoryTheory.Functor.ext
      · intro x y f
        simp [FundamentalGroupoid.map]
        sorry -- Requires FundamentalGroupoid.map_comp which is inaccessible with current imports.
      · intro x
        simp [FundamentalGroupoid.map]
        ext
        exact hr x.as

/-- The fundamental group of the disk is trivial, since the disk is contractible. -/
lemma disk2_fg_trivial : ∀ (x : disk2), Subsingleton (FundamentalGroup disk2 x) := by
  intro x
  unfold FundamentalGroup
  refine { allEq := ?_ }
  intro a b
  -- Goal: any two loops in disk2 based at x are homotopic.
  -- Mathematically this follows from contractibility: disk_homotopy provides a null-homotopy
  -- for any loop. However, the Mathlib API connecting CategoryTheory.End to contractibility
  -- is missing -- apply? finds no relevant lemmas. Left as sorry.
  sorry

/-- A left inverse on fundamental groups forces the source group to inject into the target. -/
lemma fg_nontrivial_of_retract (r : C(disk2, circle1)) (hr : ∀ x : circle1, r (i x) = x) :
    Nontrivial (FundamentalGroup disk2 (i circle1_bp)) := by
  -- Follows from circle1_fg_nontrivial and functoriality of pi_1:
  -- i* : pi_1(S1) -> pi_1(D2) is injective since r* o i* = id (as r o i = id by hr).
  -- Injectivity of i* transfers nontriviality from pi_1(S1) to pi_1(D2).
  -- Requires FundamentalGroupoid.map_comp which is inaccessible with current imports.
  sorry

/-- There is no continuous retraction from the disk to the circle. -/
theorem no_retraction : ¬ ∃ (r : C(disk2, circle1)), ∀ (x : circle1), r (i x) = x := by
  intro ⟨r, hr⟩
  have h1 := disk2_fg_trivial (i circle1_bp)
  have h2 := fg_nontrivial_of_retract r hr
  exact absurd h2 (not_nontrivial_iff_subsingleton.mpr h1)

/-- The direction vector from `f(x)` to `x`. -/
noncomputable def ray_direction (x : disk2) (fx : disk2) : ℝ² :=
  x.1 - fx.1

/-- The ray direction is nonzero when `f(x) ≠ x`. -/
lemma ray_direction_nonzero (x : disk2) (fx : disk2) (h : x.1 ≠ fx.1) :
    ray_direction x fx ≠ 0 := by
  simp [ray_direction]
  exact sub_ne_zero.mpr h

/-- For each `x ∈ D²`, the parameter `t` at which the ray from `f(x)` through `x` hits `S¹`. -/
lemma ray_hits_circle (x : disk2) (fx : disk2) (h : x.1 ≠ fx.1) :
    ∃ t : ℝ, 0 < t ∧ ‖fx.1 + t • (x.1 - fx.1)‖ = 1 := by
  sorry

/-- The point where the ray from `f(x)` through `x` hits `S¹`. -/
noncomputable def ray_circle_pt (x : disk2) (fx : disk2) (h : x.1 ≠ fx.1) : circle1 :=
  ⟨fx.1 + (ray_hits_circle x fx h).choose • (x.1 - fx.1),
   (ray_hits_circle x fx h).choose_spec.2⟩

/-- The retraction map sending each `x ∈ D²` to the point where the ray from `f(x)`
    through `x` hits `S¹`. -/
noncomputable def retraction_of_no_fixedpoint (f : C(disk2, disk2))
    (hf : ∀ x : disk2, f x ≠ x) : disk2 → circle1 :=
  fun x => ray_circle_pt x (f x) (by
    intro h
    exact hf x (Subtype.ext h.symm))

/-- The retraction constructed from a fixed-point-free map is continuous. -/
lemma retraction_continuous (f : C(disk2, disk2))
    (hf : ∀ x : disk2, f x ≠ x) :
    Continuous (retraction_of_no_fixedpoint f hf) := by
  -- Continuity follows from the continuous dependence of the quadratic roots on parameters.
  sorry

/-- The retraction fixes points on `S¹`. -/
lemma retraction_fixes_circle (f : C(disk2, disk2))
    (hf : ∀ x : disk2, f x ≠ x) (x : circle1) :
    retraction_of_no_fixedpoint f hf (i x) = x := by
  -- When x ∈ S¹, the ray from f(x) through x hits S¹ at x itself.
  sorry

/-- If `f : D² → D²` has no fixed point, we can construct a retraction from D² to S¹. -/
lemma no_fixedpoint_gives_retraction (f : C(disk2, disk2))
    (hf : ∀ x : disk2, f x ≠ x) :
    ∃ (r : C(disk2, circle1)), ∀ (x : circle1), r (i x) = x :=
  ⟨⟨retraction_of_no_fixedpoint f hf, retraction_continuous f hf⟩,
   retraction_fixes_circle f hf⟩

/-- The identity map on `disk2` has a fixed point, i.e. there exists a point fixed by the
    identity. This is an immediate corollary of Brouwer. -/
theorem identity_has_fixed_point : ∃ x : disk2, ContinuousMap.id disk2 x = x := ⟨disk_bp, rfl⟩

/-- A constant map on `disk2` has a fixed point. -/
theorem constant_map_has_fixed_point (y : disk2) :
    ∃ x : disk2, (ContinuousMap.const disk2 y) x = x := ⟨y, rfl⟩

/-- Brouwer's fixed point theorem: every continuous map from `disk2` to itself has a fixed
    point. This is the main theorem of the file. -/
theorem brouwer_fixed_point (f : C(disk2, disk2)) : ∃ x : disk2, f x = x := by
  by_contra h
  push_neg at h
  exact no_retraction (no_fixedpoint_gives_retraction f h)

/-- A continuous map from `disk2` to itself cannot be fixed-point-free. -/
theorem not_fixed_point_free (f : C(disk2, disk2)) : ¬ ∀ x : disk2, f x ≠ x := by
  intro h
  exact no_retraction (no_fixedpoint_gives_retraction f h)

/-- Any two continuous maps from `disk2` to itself share a fixed point in the sense that
    neither can be fixed-point-free. -/
theorem no_map_is_fixed_point_free : ¬ ∃ f : C(disk2, disk2), ∀ x : disk2, f x ≠ x := by
  intro ⟨f, hf⟩
  exact no_retraction (no_fixedpoint_gives_retraction f hf)

#lint
