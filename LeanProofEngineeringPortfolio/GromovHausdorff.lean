/-
copyright (c) 2026 Atif Sarwar Sayed. All rights reserved.
Authors: Atif Sarwar Sayed
-/
import Mathlib.Topology.MetricSpace.Defs

/-!
# Hausdorff and Gromov-Hausdorff distance

In this file we introduce the `Hausdorff` distance between subsets of a metric spaces.
Our main result is that the space of all subsets of a metric space, endowed with the
`Hausdorff` distance is a pseudo-metric space.

## References

- [Burago, D., Burago, Y., & Ivanov, S. (2001). A course in metric geometry. American Mathematical
Society.]
-/

open MetricSpace

variable {α : Type} [MetricSpace α]
  -- I was given feedback during labs to use the implicit argument notation for the type as it was
   -- I was getting a type-mismatch in def d_H (Otherwise I had to supply the type α explicitly).

-- We first introduce the `Hausdorff` distance between subsets of a metric space.

section HausdorffDistance

/-- ball of radius r around a point in A. -/
def B (r : ℝ) (a : α) (A : Set α) : Set α :=
  {x | a ∈ A ∧ dist x a ≤ r}

/-- r-neighborhood of a set A. -/
def U (r : ℝ) (A : Set α) : Set α :=
  ⋃ a ∈ A, B r a A
    -- was using ':' instead of '|' after x ∈ A, was flagged.
     -- was using '(hr :r ≥ 0)' in the definition, but 'dist' is by def non-negative.
      -- defined this as I was getting an error.

-- having to prove some annoyingly basic lemmas about containment of `a` and `A` in `U r A`.
lemma U_contains_a (r : ℝ) (A : Set α) (a : α) (hr : r ≥ 0) : a ∈ A → a ∈ U r A := by
  intro ha
  rw [U]
  change a ∈ ⋃ b ∈ A, B r b A
  apply Set.mem_biUnion  -- source: Moogle.ai, searched for membership in a union.
  exact ha
  -- rw [B], didn't need this, not sure why.
  use ha -- couldn't use "use a" because a has type α, but I need it to have type "a ∈ A".
  simp
  exact hr --or grind, but that doesn't exactly reduce work!

-- r-neighborhood of a set A, contains A.
lemma U_contains_A (A : Set α) (r : ℝ) (hr : r ≥ 0) : A ⊆ U r A := by
  intro x hx
  apply U_contains_a r A x hr
  exact hx

/-- defining the set on which we are taking the infimum to define the Hausdorff distance. -/
def S (A B : Set α) : Set ℝ :=
  {r | r ≥ 0 ∧ A ⊆ U r B ∧ B ⊆ U r A}
  -- Writing "U r A", instead of "U_r(A)" as the latter would just be the name of the function.
   -- The former would treat it as a function. (Lab feedback).

/-- The Hausdorff distance between two subsets A and B. -/
noncomputable def d_H (A B : Set α) : ℝ :=
  sInf (S A B)
   -- Changed InfSet to sInf (lab feedback) as the former talks about all infimum structures on
    -- the set, hence the type being Type. The latter considers the set as a subset of the reals,
     -- giving me what I want.
   -- Also made the definition noncomputable (lab feedback).

-- A few results about the Hausdorff distance.

lemma d_H_nonneg (A B : Set α): d_H A B ≥ 0 := by
 rw [d_H]  -- rw changes the goal to the definition of d_H, which is sInf (S A B).
 apply Real.sInf_nonneg   -- (Source: Moogle.ai). Now I just show S A B is bounded below by 0.
 intro r hr
 exact hr.1               -- hr.1 considers the first part of a ∧ b. So it considers the first part
                          -- in def S A B.

lemma SAB_Symmetric (A B : Set α) (h : ∀ r, r ∈ S A B ↔ r ∈ S B A) : S A B = S B A := by
  ext r
  apply h

lemma d_H_symmetric (A B : Set α) (h : ∀ r, r ∈ S A B ↔ r ∈ S B A) : d_H A B = d_H B A := by
  rw [d_H, d_H]
  rw [SAB_Symmetric A B]
  exact h

lemma Ur1r2_subset_Ur1_plus_r2 (A : Set α) (r1 r2 : ℝ) :
  U r1 (U r2 A) ⊆ U (r1 + r2) A := by
  intro x hx
  rw [U, Set.mem_iUnion₂] at hx  -- rw [U, Set.mem_iUnion₂], instead of rw [U], to get a cleaner
                                  -- InfoView. Got this idea from Gemini. Set.mem_iUnion₂
                                   --simplifies nested unions.
  rcases hx with ⟨a, ha_in_U, hx_in_B⟩
  rw [U, Set.mem_iUnion₂] at ha_in_U  -- applied the same trick again.
  rcases ha_in_U with ⟨y, hy_in_A, ha_in_By⟩
  have hxa : dist x a ≤ r1 := hx_in_B.2  -- realizing now that I shouldn't have included the
                                          --`a ∈ A` in the definition of a ball!
  have hay : dist a y ≤ r2 := ha_in_By.2
  rw [U]
  apply Set.mem_biUnion hy_in_A  -- Set.mem_iUnion₂ doesn't work for some reason..
  rw [B]
  constructor
  · exact hy_in_A
  · have h_tri : dist x y ≤ dist x a + dist a y := dist_triangle x a y
    linarith -- combines hxa, hxy and h_tri.

lemma subset (A B C : Set α) (r1 r2 : ℝ) (hr1 : r1 ∈ S A B) (hr2 : r2 ∈ S B C) :
  r1 + r2 ∈ S A C := by -- to show: S A B + S B C is a subset of S A C. This would imply that
                         -- the infimum of the former is greater than or equal to the infimum
                          -- of the latter, helping me prove the triangle inequality for d_H.

  rw [S]
  constructor
  · rw [S] at hr1 hr2
    rcases hr1 with ⟨hr1_nonneg, hr1_AB_BA⟩
    rcases hr2 with ⟨hr2_nonneg, hr2_BC_CB⟩
    linarith
  . rw [S] at hr1 hr2
    rcases hr1 with ⟨hr1_nonneg, hr1_AB, hr1_BA⟩
    rcases hr2 with ⟨hr2_nonneg, hr2_BC, hr2_CB⟩
    -- I need to now show that A ⊆ U (r1 + r2) C and C ⊆ U (r1 + r2) A.
     -- However, from what I have, I know that, WLOG, A ⊆ U r1 (U r2 C). Therefore I just need
      -- to show that the latter is a subset of U (r1 + r2) C. This has been done in the
       --previous lemma.
    constructor
    · calc  -- got the idea of a calc block from Gemini. Very convenient to do computations.
       -- in this first block I show that A ⊆ U r1 ( U r2 C). It ends with showing
        --U r1 (U r2 C) ⊆ U (r1 + r2) C, using `_` to call the former containment.
         --The first two lines are ideas from Gemini.
       A ⊆ U r1 B := hr1_AB
       _ ⊆ U r1 (U r2 C) := by  -- the `_` denotes the previous containment and "calls" U r1 B.
        intro x hx
        rw [U, Set.mem_iUnion₂] at hx ⊢
        rcases hx with ⟨b, hb_in_B, hx_in_Bb⟩
        use b
        rw [_root_.B] at hx_in_Bb ⊢
        constructor
        · constructor
          · apply hr2_BC
            exact hb_in_B
          · exact hx_in_Bb.2
        · exact hr2_BC hb_in_B
       _ ⊆ U (r1 + r2) C := Ur1r2_subset_Ur1_plus_r2 C r1 r2
    · calc
       C ⊆ U r2 B := hr2_CB
       _ ⊆ U r2 (U r1 A) := by
        intro x hx
        rw [U, Set.mem_iUnion₂] at hx ⊢
        rcases hx with ⟨c, hc_in_C, hx_in_Cc⟩
        use c
        rw [_root_.B] at hx_in_Cc ⊢
        constructor
        · constructor
          · apply hr1_BA
            exact hc_in_C
          · exact hx_in_Cc.2
        · exact hr1_BA hc_in_C
       _ ⊆ U (r1 + r2) A := by
           rw [add_comm]
           exact Ur1r2_subset_Ur1_plus_r2 A r2 r1


lemma d_H_triangle (A B C : Set α) :
  d_H A C ≤ d_H A B + d_H B C := by
  rw [d_H, d_H, d_H]
  sorry

-- It follows that the space of subsets of a metric space equipped with the `Hausdorff` distance
 --is a pseudo-metric space.

lemma SAA_has_0 (A : Set α) : 0 ∈ S A A := by
  rw [S]
  constructor
  · grind
  · constructor
    · rw [U]
      intro x hx
      apply U_contains_A A 0  -- assuming r=0 made hr obsolete, hence not needed to call the lemma.
      trivial
      exact hx
    · apply U_contains_A A
      trivial

noncomputable instance : PseudoMetricSpace (Set α) where
  dist := d_H
  dist_self A := by
    apply le_antisymm  -- d_H A A = 0 iff d_H A A ≥ 0 and d_H A A ≤ 0
    rw [d_H]
    apply csInf_le  -- apparently ℝ is a not a complete lattice so sInf_le doesn't work.
                     --It is however a conditionally complete lattice and csInf_le works (Moogle.ai)
    use 0
    intro r hr
    exact hr.1
    apply SAA_has_0
    exact d_H_nonneg A A
  dist_comm A B := by
    apply d_H_symmetric
    intro r
    rw [S, S]
    grind
  dist_triangle A B C := by
    apply d_H_triangle A B C

#lint

#min_imports
