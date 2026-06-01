/-
Self-contained Lean4Web paste file.
Block 355 real-log V_i(y) > 0 check for the M=1.817475 candidate.

This file includes the rational kernel, the generated block data,
and the Mathlib Real.log bridge.  The final #check lines expose
the block-level theorem whose type contains `0 < block...V y`.

This is still only a block-level reduced-certificate check: it
does not formalize the outer reduction from the original #1038
problem, and the theorem excludes the singular atom locations.
-/

import Mathlib


/-!
# Rational box kernel for #1038 finite-atom checks

This file is deliberately Mathlib-free.  It does not prove the analytic
`Real.log` bridge.  It proves the finite arithmetic part that should later be
connected to `Real.log` by a Mathlib file, following the Hua Xu certificate
architecture.
-/

namespace Erdos1038Lean

def ratAbs (x : Rat) : Rat :=
  if x < 0 then -x else x

def atanhLowerRat : Nat -> Rat -> Rat
  | 0, _ => 0
  | n + 1, t => atanhLowerRat n t + 2 * t ^ (2 * n + 1) / (2 * n + 1)

def atanhUpperRat (n : Nat) (t : Rat) : Rat :=
  atanhLowerRat n t + 2 * t ^ (2 * n + 1) / (1 - t ^ 2)

def tInv (d : Rat) : Rat := (1 - d) / (1 + d)

def tSelf (d : Rat) : Rat := (d - 1) / (d + 1)

def logInvLowerRat (nPos nNeg : Nat) (d : Rat) : Rat :=
  if d < 1 then
    atanhLowerRat nPos (tInv d)
  else
    -atanhUpperRat nNeg (tSelf d)

structure RatBox where
  w1 : Rat
  w2 : Rat
  w3 : Rat
  w4 : Rat
  s1 : Rat
  s2 : Rat
  s3 : Rat
  s4 : Rat
  L : Rat
  R : Rat
  D0 : Rat
  D1 : Rat
  D2 : Rat
  D3 : Rat
  D4 : Rat
  LB : Rat
  deriving DecidableEq, Repr

def RatBox.computedLower (b : RatBox) (nPos nNeg : Nat := 150) : Rat :=
  logInvLowerRat nPos nNeg b.D0
  + b.w1 * logInvLowerRat nPos nNeg b.D1
  + b.w2 * logInvLowerRat nPos nNeg b.D2
  + b.w3 * logInvLowerRat nPos nNeg b.D3
  + b.w4 * logInvLowerRat nPos nNeg b.D4

def RatBox.validFastBool (b : RatBox) : Bool :=
  decide (
    0 <= b.w1 /\ 0 <= b.w2 /\ 0 <= b.w3 /\ 0 <= b.w4 /\
    b.L <= b.R /\
    0 < b.D0 /\ 0 < b.D1 /\ 0 < b.D2 /\ 0 < b.D3 /\ 0 < b.D4 /\
    0 < b.LB /\
    ratAbs (b.L - 0) <= b.D0 /\ ratAbs (b.R - 0) <= b.D0 /\
    ratAbs (b.L - b.s1) <= b.D1 /\ ratAbs (b.R - b.s1) <= b.D1 /\
    ratAbs (b.L - b.s2) <= b.D2 /\ ratAbs (b.R - b.s2) <= b.D2 /\
    ratAbs (b.L - b.s3) <= b.D3 /\ ratAbs (b.R - b.s3) <= b.D3 /\
    ratAbs (b.L - b.s4) <= b.D4 /\ ratAbs (b.R - b.s4) <= b.D4)

def RatBox.validComputedBool (b : RatBox) (nPos nNeg : Nat := 150) : Bool :=
  b.validFastBool && decide (b.LB = b.computedLower nPos nNeg)

def RatBox.validComputedPositiveBool (b : RatBox) (nPos nNeg : Nat := 150) : Bool :=
  b.validFastBool && decide (0 < b.computedLower nPos nNeg)

def allBoxesFastValid (boxes : List RatBox) : Bool :=
  boxes.all (fun b => b.validFastBool)

def allBoxesComputedValid (boxes : List RatBox) (nPos nNeg : Nat := 150) : Bool :=
  boxes.all (fun b => b.validComputedBool nPos nNeg)

def allBoxesComputedPositiveValid (boxes : List RatBox) (nPos nNeg : Nat := 150) : Bool :=
  boxes.all (fun b => b.validComputedPositiveBool nPos nNeg)

def allBoxesValid (boxes : List RatBox) : Bool :=
  allBoxesComputedPositiveValid boxes 150 150

def coversFromBool : List RatBox -> Rat -> Rat -> Bool
  | [], _lo, _hi => false
  | [b], lo, hi => decide (b.L <= lo /\ hi <= b.R)
  | b :: b' :: bs, lo, hi =>
      decide (b.L <= lo /\ lo <= b.R) && coversFromBool (b' :: bs) b.R hi

def boxCount (xs : List RatBox) : Nat := xs.length

def worstLower? (boxes : List RatBox) : Option Rat :=
  match boxes.map (fun b => b.LB) with
  | [] => none
  | x :: xs => some (xs.foldl min x)

end Erdos1038Lean


/-!
# Real-log bridge for rational boxes

This file starts the Mathlib layer connecting the exact rational box checks to
actual logarithmic potentials over `ℝ`.

The pure certificate files check each `RatBox` by exact rational arithmetic.
Here we prove the reusable analytic bridge for one rational box: if Lean has
checked a positive computed rational lower bound, then the corresponding
five-term real logarithmic potential is positive on the box, away from the
singular atom locations.
-/

namespace Erdos1038Lean

noncomputable section

open Finset Set

lemma bool_left_of_and_eq_true {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

lemma bool_right_of_and_eq_true {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

def atanhLowerReal (n : Nat) (t : ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * (i : ℝ) + 1))

def atanhUpperReal (n : Nat) (t : ℝ) : ℝ :=
  atanhLowerReal n t + 2 * t ^ (2 * n + 1) / (1 - t ^ 2)

lemma atanhLowerRat_cast (n : Nat) (t : Rat) :
    ((atanhLowerRat n t : Rat) : ℝ) = atanhLowerReal n (t : ℝ) := by
  induction n with
  | zero =>
      simp [atanhLowerRat, atanhLowerReal]
  | succ n ih =>
      rw [atanhLowerRat]
      simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
      rw [ih]
      simp [atanhLowerReal, Finset.sum_range_succ]
      ring

lemma atanhUpperRat_cast (n : Nat) (t : Rat) :
    ((atanhUpperRat n t : Rat) : ℝ) = atanhUpperReal n (t : ℝ) := by
  simp [atanhUpperRat, atanhUpperReal, atanhLowerRat_cast]

lemma atanhLowerRat_le_log_of_mobius
    (r t : Rat) (n : Nat)
    (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hr : (r : ℝ) = (1 + (t : ℝ)) / (1 - (t : ℝ))) :
    ((atanhLowerRat n t : Rat) : ℝ) ≤ Real.log (r : ℝ) := by
  have h := Real.sum_range_le_log_div ht0 ht1 n
  rw [atanhLowerRat_cast]
  unfold atanhLowerReal
  rw [hr]
  nlinarith

lemma log_le_atanhUpperRat_of_mobius
    (r t : Rat) (n : Nat)
    (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hr : (r : ℝ) = (1 + (t : ℝ)) / (1 - (t : ℝ))) :
    Real.log (r : ℝ) ≤ ((atanhUpperRat n t : Rat) : ℝ) := by
  have h := Real.log_div_le_sum_range_add ht0 ht1 n
  rw [atanhUpperRat_cast]
  unfold atanhUpperReal atanhLowerReal
  rw [hr]
  have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.log ((1 + (t : ℝ)) / (1 - (t : ℝ)))
        = 2 * (1 / 2 * Real.log ((1 + (t : ℝ)) / (1 - (t : ℝ)))) := by ring
    _ ≤ 2 * (∑ i ∈ Finset.range n,
          (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)
        + (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2)) := h2
    _ = 2 * ∑ i ∈ Finset.range n,
          (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)
        + 2 * (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2) := by ring

lemma tInv_cast_eq (d : Rat) :
    (tInv d : ℝ) = (1 - (d : ℝ)) / (1 + (d : ℝ)) := by
  unfold tInv
  norm_num

lemma tSelf_cast_eq (d : Rat) :
    (tSelf d : ℝ) = ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
  unfold tSelf
  norm_num

lemma logInvLowerRat_le_log_inv (nPos nNeg : Nat) (d : Rat) (hd : 0 < d) :
    ((logInvLowerRat nPos nNeg d : Rat) : ℝ) ≤ Real.log ((d : ℝ)⁻¹) := by
  by_cases hlt : d < 1
  · simp [logInvLowerRat, hlt]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hltR : (d : ℝ) < 1 := by exact_mod_cast hlt
    have htEq := tInv_cast_eq d
    have hden : 0 < 1 + (d : ℝ) := by positivity
    have ht0 : 0 ≤ (tInv d : ℝ) := by
      rw [htEq]
      exact div_nonneg (sub_nonneg.mpr hltR.le) hden.le
    have ht1 : (tInv d : ℝ) < 1 := by
      rw [htEq]
      field_simp [hden.ne']
      linarith
    have hr : ((1 / d : Rat) : ℝ) =
        (1 + (tInv d : ℝ)) / (1 - (tInv d : ℝ)) := by
      rw [htEq]
      norm_num
      field_simp [show (d : ℝ) ≠ 0 by positivity, hden.ne']
      ring
    simpa using atanhLowerRat_le_log_of_mobius (1 / d) (tInv d) nPos ht0 ht1 hr
  · simp [logInvLowerRat, hlt]
    have hge : (1 : Rat) ≤ d := le_of_not_gt hlt
    have hgeR : (1 : ℝ) ≤ d := by exact_mod_cast hge
    have htEq := tSelf_cast_eq d
    have hden : 0 < (d : ℝ) + 1 := by positivity
    have ht0 : 0 ≤ (tSelf d : ℝ) := by
      rw [htEq]
      exact div_nonneg (sub_nonneg.mpr hgeR) hden.le
    have ht1 : (tSelf d : ℝ) < 1 := by
      rw [htEq]
      field_simp [hden.ne']
      linarith
    have hr : (d : ℝ) =
        (1 + (tSelf d : ℝ)) / (1 - (tSelf d : ℝ)) := by
      rw [htEq]
      field_simp [hden.ne']
      ring
    exact log_le_atanhUpperRat_of_mobius d (tSelf d) nNeg ht0 ht1 hr

lemma logInvLowerRat_le_log_actual_inv
    (nPos nNeg : Nat) (d : Rat) {actual : ℝ}
    (hd : 0 < d) (hactual : 0 < actual) (hle : actual ≤ (d : ℝ)) :
    ((logInvLowerRat nPos nNeg d : Rat) : ℝ) ≤ Real.log actual⁻¹ := by
  have hbase := logInvLowerRat_le_log_inv nPos nNeg d hd
  have hdinv : ((d : ℝ)⁻¹) ≤ actual⁻¹ := by
    exact (inv_le_inv₀ (by exact_mod_cast hd : (0 : ℝ) < d) hactual).2 hle
  exact hbase.trans (Real.log_le_log (inv_pos.mpr (by exact_mod_cast hd)) hdinv)

lemma ratAbs_cast (x : Rat) :
    ((ratAbs x : Rat) : ℝ) = |(x : ℝ)| := by
  unfold ratAbs
  by_cases hx : x < 0
  · simp [hx]
    have hxR : (x : ℝ) < 0 := by exact_mod_cast hx
    rw [abs_of_neg hxR]
  · simp [hx]
    have hxR : 0 ≤ (x : ℝ) := by exact_mod_cast le_of_not_gt hx
    rw [abs_of_nonneg hxR]

lemma real_abs_bound_of_ratAbs {x D : Rat}
    (h : ratAbs x ≤ D) :
    |(x : ℝ)| ≤ (D : ℝ) := by
  have hc : ((ratAbs x : Rat) : ℝ) ≤ (D : ℝ) := by exact_mod_cast h
  simpa [ratAbs_cast] using hc

lemma abs_sub_le_of_box_endpoints
    {L R p D y : ℝ}
    (hy : y ∈ Icc L R)
    (hL : |L - p| ≤ D)
    (hR : |R - p| ≤ D) :
    |y - p| ≤ D := by
  rw [abs_sub_le_iff] at hL hR ⊢
  constructor <;> linarith [hy.1, hy.2, hL.1, hL.2, hR.1, hR.2]

def RatBox.realPotential (b : RatBox) (y : ℝ) : ℝ :=
    Real.log (|y|)⁻¹
  + (b.w1 : ℝ) * Real.log (|y - (b.s1 : ℝ)|)⁻¹
  + (b.w2 : ℝ) * Real.log (|y - (b.s2 : ℝ)|)⁻¹
  + (b.w3 : ℝ) * Real.log (|y - (b.s3 : ℝ)|)⁻¹
  + (b.w4 : ℝ) * Real.log (|y - (b.s4 : ℝ)|)⁻¹

def ratPotential
    (w1 w2 w3 w4 s1 s2 s3 s4 : Rat) (y : ℝ) : ℝ :=
    Real.log (|y|)⁻¹
  + (w1 : ℝ) * Real.log (|y - (s1 : ℝ)|)⁻¹
  + (w2 : ℝ) * Real.log (|y - (s2 : ℝ)|)⁻¹
  + (w3 : ℝ) * Real.log (|y - (s3 : ℝ)|)⁻¹
  + (w4 : ℝ) * Real.log (|y - (s4 : ℝ)|)⁻¹

def RatBox.sameParamsBool
    (b : RatBox) (w1 w2 w3 w4 s1 s2 s3 s4 : Rat) : Bool :=
  decide (
    b.w1 = w1 /\ b.w2 = w2 /\ b.w3 = w3 /\ b.w4 = w4 /\
    b.s1 = s1 /\ b.s2 = s2 /\ b.s3 = s3 /\ b.s4 = s4)

def allBoxesSameParams
    (boxes : List RatBox) (w1 w2 w3 w4 s1 s2 s3 s4 : Rat) : Bool :=
  boxes.all (fun b => b.sameParamsBool w1 w2 w3 w4 s1 s2 s3 s4)

lemma RatBox.sameParamsBool_eq_true_iff
    (b : RatBox) (w1 w2 w3 w4 s1 s2 s3 s4 : Rat) :
    b.sameParamsBool w1 w2 w3 w4 s1 s2 s3 s4 = true ↔
      b.w1 = w1 /\ b.w2 = w2 /\ b.w3 = w3 /\ b.w4 = w4 /\
      b.s1 = s1 /\ b.s2 = s2 /\ b.s3 = s3 /\ b.s4 = s4 := by
  unfold RatBox.sameParamsBool
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

lemma RatBox.realPotential_eq_ratPotential_of_sameParams
    {b : RatBox} {w1 w2 w3 w4 s1 s2 s3 s4 : Rat}
    (h : b.sameParamsBool w1 w2 w3 w4 s1 s2 s3 s4 = true) :
    b.realPotential = ratPotential w1 w2 w3 w4 s1 s2 s3 s4 := by
  rcases (b.sameParamsBool_eq_true_iff w1 w2 w3 w4 s1 s2 s3 s4).mp h with
    ⟨hw1, hw2, hw3, hw4, hs1, hs2, hs3, hs4⟩
  funext y
  simp [RatBox.realPotential, ratPotential, hw1, hw2, hw3, hw4, hs1, hs2, hs3, hs4]

lemma sameParamsBool_of_mem_allBoxesSameParams
    {boxes : List RatBox} {b : RatBox} {w1 w2 w3 w4 s1 s2 s3 s4 : Rat}
    (hparams : allBoxesSameParams boxes w1 w2 w3 w4 s1 s2 s3 s4 = true)
    (hb : b ∈ boxes) :
    b.sameParamsBool w1 w2 w3 w4 s1 s2 s3 s4 = true := by
  unfold allBoxesSameParams at hparams
  exact List.all_eq_true.mp hparams b hb

lemma RatBox.computedLower_le_realPotential
    (b : RatBox) (nPos nNeg : Nat) {y : ℝ}
    (hw1 : 0 ≤ (b.w1 : ℝ))
    (hw2 : 0 ≤ (b.w2 : ℝ))
    (hw3 : 0 ≤ (b.w3 : ℝ))
    (hw4 : 0 ≤ (b.w4 : ℝ))
    (hD0 : 0 < b.D0) (hD1 : 0 < b.D1) (hD2 : 0 < b.D2)
    (hD3 : 0 < b.D3) (hD4 : 0 < b.D4)
    (hy0 : 0 < |y|)
    (hy1 : 0 < |y - (b.s1 : ℝ)|)
    (hy2 : 0 < |y - (b.s2 : ℝ)|)
    (hy3 : 0 < |y - (b.s3 : ℝ)|)
    (hy4 : 0 < |y - (b.s4 : ℝ)|)
    (hb0 : |y| ≤ (b.D0 : ℝ))
    (hb1 : |y - (b.s1 : ℝ)| ≤ (b.D1 : ℝ))
    (hb2 : |y - (b.s2 : ℝ)| ≤ (b.D2 : ℝ))
    (hb3 : |y - (b.s3 : ℝ)| ≤ (b.D3 : ℝ))
    (hb4 : |y - (b.s4 : ℝ)| ≤ (b.D4 : ℝ)) :
    ((b.computedLower nPos nNeg : Rat) : ℝ) ≤ b.realPotential y := by
  have h0 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D0 hD0 hy0 hb0
  have h1 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D1 hD1 hy1 hb1
  have h2 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D2 hD2 hy2 hb2
  have h3 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D3 hD3 hy3 hb3
  have h4 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D4 hD4 hy4 hb4
  have h1w :
      (b.w1 : ℝ) * ((logInvLowerRat nPos nNeg b.D1 : Rat) : ℝ)
        ≤ (b.w1 : ℝ) * Real.log (|y - (b.s1 : ℝ)|)⁻¹ :=
    mul_le_mul_of_nonneg_left h1 hw1
  have h2w :
      (b.w2 : ℝ) * ((logInvLowerRat nPos nNeg b.D2 : Rat) : ℝ)
        ≤ (b.w2 : ℝ) * Real.log (|y - (b.s2 : ℝ)|)⁻¹ :=
    mul_le_mul_of_nonneg_left h2 hw2
  have h3w :
      (b.w3 : ℝ) * ((logInvLowerRat nPos nNeg b.D3 : Rat) : ℝ)
        ≤ (b.w3 : ℝ) * Real.log (|y - (b.s3 : ℝ)|)⁻¹ :=
    mul_le_mul_of_nonneg_left h3 hw3
  have h4w :
      (b.w4 : ℝ) * ((logInvLowerRat nPos nNeg b.D4 : Rat) : ℝ)
        ≤ (b.w4 : ℝ) * Real.log (|y - (b.s4 : ℝ)|)⁻¹ :=
    mul_le_mul_of_nonneg_left h4 hw4
  calc
    ((b.computedLower nPos nNeg : Rat) : ℝ)
        = ((logInvLowerRat nPos nNeg b.D0 : Rat) : ℝ)
          + (b.w1 : ℝ) * ((logInvLowerRat nPos nNeg b.D1 : Rat) : ℝ)
          + (b.w2 : ℝ) * ((logInvLowerRat nPos nNeg b.D2 : Rat) : ℝ)
          + (b.w3 : ℝ) * ((logInvLowerRat nPos nNeg b.D3 : Rat) : ℝ)
          + (b.w4 : ℝ) * ((logInvLowerRat nPos nNeg b.D4 : Rat) : ℝ) := by
            simp [RatBox.computedLower]
    _ ≤ Real.log (|y|)⁻¹
          + (b.w1 : ℝ) * Real.log (|y - (b.s1 : ℝ)|)⁻¹
          + (b.w2 : ℝ) * Real.log (|y - (b.s2 : ℝ)|)⁻¹
          + (b.w3 : ℝ) * Real.log (|y - (b.s3 : ℝ)|)⁻¹
          + (b.w4 : ℝ) * Real.log (|y - (b.s4 : ℝ)|)⁻¹ := by
            nlinarith
    _ = b.realPotential y := by
            simp [RatBox.realPotential]

lemma RatBox.validFastBool_eq_true_iff (b : RatBox) :
    b.validFastBool = true ↔
      0 ≤ b.w1 ∧ 0 ≤ b.w2 ∧ 0 ≤ b.w3 ∧ 0 ≤ b.w4 ∧
      b.L ≤ b.R ∧
      0 < b.D0 ∧ 0 < b.D1 ∧ 0 < b.D2 ∧ 0 < b.D3 ∧ 0 < b.D4 ∧
      0 < b.LB ∧
      ratAbs (b.L - 0) ≤ b.D0 ∧ ratAbs (b.R - 0) ≤ b.D0 ∧
      ratAbs (b.L - b.s1) ≤ b.D1 ∧ ratAbs (b.R - b.s1) ≤ b.D1 ∧
      ratAbs (b.L - b.s2) ≤ b.D2 ∧ ratAbs (b.R - b.s2) ≤ b.D2 ∧
      ratAbs (b.L - b.s3) ≤ b.D3 ∧ ratAbs (b.R - b.s3) ≤ b.D3 ∧
      ratAbs (b.L - b.s4) ≤ b.D4 ∧ ratAbs (b.R - b.s4) ≤ b.D4 := by
  unfold RatBox.validFastBool
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

lemma RatBox.validComputedPositiveBool_eq_true_iff
    (b : RatBox) (nPos nNeg : Nat) :
    b.validComputedPositiveBool nPos nNeg = true ↔
      b.validFastBool = true ∧ 0 < b.computedLower nPos nNeg := by
  unfold RatBox.validComputedPositiveBool
  constructor
  · intro h
    by_cases hfast : b.validFastBool = true
    · constructor
      · exact hfast
      · rw [hfast] at h
        simp at h
        exact h
    · have hfastFalse : b.validFastBool = false := by
        cases hb : b.validFastBool <;> simp_all
      rw [hfastFalse] at h
      simp at h
  · intro h
    rw [h.1]
    simp [decide_eq_true h.2]

lemma validComputedPositiveBool_of_mem_allBoxesValid
    {boxes : List RatBox} {b : RatBox}
    (hboxes : allBoxesValid boxes = true)
    (hb : b ∈ boxes) :
    b.validComputedPositiveBool 150 150 = true := by
  unfold allBoxesValid allBoxesComputedPositiveValid at hboxes
  exact List.all_eq_true.mp hboxes b hb

lemma exists_mem_box_of_coversFromBool
    {boxes : List RatBox} {lo hi : Rat}
    (hcovers : coversFromBool boxes lo hi = true)
    {y : ℝ} (hy : y ∈ Icc (lo : ℝ) (hi : ℝ)) :
    ∃ b ∈ boxes, y ∈ Icc (b.L : ℝ) (b.R : ℝ) := by
  induction boxes generalizing lo with
  | nil =>
      simp [coversFromBool] at hcovers
  | cons b bs ih =>
      cases bs with
      | nil =>
          have hprop : b.L ≤ lo ∧ hi ≤ b.R := by
            have hdec : decide (b.L ≤ lo ∧ hi ≤ b.R) = true := by
              simpa [coversFromBool] using hcovers
            exact of_decide_eq_true hdec
          rcases hprop with ⟨hbL, hhiR⟩
          refine ⟨b, by simp, ?_⟩
          constructor
          · have hbLR : (b.L : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hbL
            linarith [hbLR, hy.1]
          · have hhiRR : (hi : ℝ) ≤ (b.R : ℝ) := by exact_mod_cast hhiR
            linarith [hhiRR, hy.2]
      | cons b' bs =>
          have hbool :
              decide (b.L ≤ lo ∧ lo ≤ b.R) &&
                  coversFromBool (b' :: bs) b.R hi = true := by
            simpa [coversFromBool] using hcovers
          have hheadBool : decide (b.L ≤ lo ∧ lo ≤ b.R) = true := by
            cases h : decide (b.L ≤ lo ∧ lo ≤ b.R) <;> simp [h] at hbool ⊢
          have hrest : coversFromBool (b' :: bs) b.R hi = true := by
            cases h : decide (b.L ≤ lo ∧ lo ≤ b.R) <;> simp [h] at hbool
            exact hbool
          have hhead : b.L ≤ lo ∧ lo ≤ b.R := of_decide_eq_true hheadBool
          rcases hhead with ⟨hbL, _hloR⟩
          by_cases hyR : y ≤ (b.R : ℝ)
          · refine ⟨b, by simp, ?_⟩
            constructor
            · have hbLR : (b.L : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hbL
              linarith [hbLR, hy.1]
            · exact hyR
          · have hbRy : (b.R : ℝ) ≤ y := le_of_lt (lt_of_not_ge hyR)
            have hy' : y ∈ Icc (b.R : ℝ) (hi : ℝ) := ⟨hbRy, hy.2⟩
            rcases ih hrest hy' with ⟨b'', hb''mem, hby⟩
            exact ⟨b'', by simp [hb''mem], hby⟩

theorem RatBox.realPotential_pos_of_validComputedPositive
    {b : RatBox} {nPos nNeg : Nat} {y : ℝ}
    (hvalid : b.validComputedPositiveBool nPos nNeg = true)
    (hy : y ∈ Icc (b.L : ℝ) (b.R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (b.s1 : ℝ))
    (hy2ne : y ≠ (b.s2 : ℝ))
    (hy3ne : y ≠ (b.s3 : ℝ))
    (hy4ne : y ≠ (b.s4 : ℝ)) :
    0 < b.realPotential y := by
  rcases (RatBox.validComputedPositiveBool_eq_true_iff b nPos nNeg).mp hvalid with
    ⟨hfast, hcomp⟩
  rcases (RatBox.validFastBool_eq_true_iff b).mp hfast with
    ⟨hw1, hw2, hw3, hw4, _hLR,
      hD0, hD1, hD2, hD3, hD4, _hLB,
      hL0, hR0, hL1, hR1, hL2, hR2, hL3, hR3, hL4, hR4⟩
  have hb0 : |y| ≤ (b.D0 : ℝ) := by
    simpa using abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := 0) (D := (b.D0 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL0)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR0)
  have hb1 : |y - (b.s1 : ℝ)| ≤ (b.D1 : ℝ) :=
    abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := (b.s1 : ℝ)) (D := (b.D1 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL1)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR1)
  have hb2 : |y - (b.s2 : ℝ)| ≤ (b.D2 : ℝ) :=
    abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := (b.s2 : ℝ)) (D := (b.D2 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL2)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR2)
  have hb3 : |y - (b.s3 : ℝ)| ≤ (b.D3 : ℝ) :=
    abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := (b.s3 : ℝ)) (D := (b.D3 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL3)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR3)
  have hb4 : |y - (b.s4 : ℝ)| ≤ (b.D4 : ℝ) :=
    abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := (b.s4 : ℝ)) (D := (b.D4 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL4)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR4)
  have hle := b.computedLower_le_realPotential nPos nNeg
    (by exact_mod_cast hw1) (by exact_mod_cast hw2)
    (by exact_mod_cast hw3) (by exact_mod_cast hw4)
    hD0 hD1 hD2 hD3 hD4
    (abs_pos.mpr hy0ne)
    (abs_pos.mpr (sub_ne_zero.mpr hy1ne))
    (abs_pos.mpr (sub_ne_zero.mpr hy2ne))
    (abs_pos.mpr (sub_ne_zero.mpr hy3ne))
    (abs_pos.mpr (sub_ne_zero.mpr hy4ne))
    hb0 hb1 hb2 hb3 hb4
  have hcompR : (0 : ℝ) < ((b.computedLower nPos nNeg : Rat) : ℝ) := by
    exact_mod_cast hcomp
  exact hcompR.trans_le hle

theorem RatBox.realPotential_pos_of_mem_allBoxesValid
    {boxes : List RatBox} {b : RatBox} {y : ℝ}
    (hboxes : allBoxesValid boxes = true)
    (hb : b ∈ boxes)
    (hy : y ∈ Icc (b.L : ℝ) (b.R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (b.s1 : ℝ))
    (hy2ne : y ≠ (b.s2 : ℝ))
    (hy3ne : y ≠ (b.s3 : ℝ))
    (hy4ne : y ≠ (b.s4 : ℝ)) :
    0 < b.realPotential y := by
  exact RatBox.realPotential_pos_of_validComputedPositive
    (validComputedPositiveBool_of_mem_allBoxesValid hboxes hb)
    hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem exists_box_realPotential_pos_of_allBoxesValid_and_covers
    {boxes : List RatBox} {lo hi : Rat} {y : ℝ}
    (hboxes : allBoxesValid boxes = true)
    (hcovers : coversFromBool boxes lo hi = true)
    (hy : y ∈ Icc (lo : ℝ) (hi : ℝ)) :
    ∃ b ∈ boxes, y ∈ Icc (b.L : ℝ) (b.R : ℝ) ∧
      (y ≠ 0 →
       y ≠ (b.s1 : ℝ) →
       y ≠ (b.s2 : ℝ) →
       y ≠ (b.s3 : ℝ) →
       y ≠ (b.s4 : ℝ) →
       0 < b.realPotential y) := by
  rcases exists_mem_box_of_coversFromBool hcovers hy with ⟨b, hb, hby⟩
  refine ⟨b, hb, hby, ?_⟩
  intro hy0 hy1 hy2 hy3 hy4
  exact b.realPotential_pos_of_mem_allBoxesValid hboxes hb hby hy0 hy1 hy2 hy3 hy4

theorem ratPotential_pos_of_allBoxesValid_covers_sameParams
    {boxes : List RatBox} {lo hi w1 w2 w3 w4 s1 s2 s3 s4 : Rat} {y : ℝ}
    (hboxes : allBoxesValid boxes = true)
    (hcovers : coversFromBool boxes lo hi = true)
    (hparams : allBoxesSameParams boxes w1 w2 w3 w4 s1 s2 s3 s4 = true)
    (hy : y ∈ Icc (lo : ℝ) (hi : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (s1 : ℝ))
    (hy2ne : y ≠ (s2 : ℝ))
    (hy3ne : y ≠ (s3 : ℝ))
    (hy4ne : y ≠ (s4 : ℝ)) :
    0 < ratPotential w1 w2 w3 w4 s1 s2 s3 s4 y := by
  rcases exists_mem_box_of_coversFromBool hcovers hy with ⟨b, hb, hby⟩
  have hbparams := sameParamsBool_of_mem_allBoxesSameParams hparams hb
  rcases (b.sameParamsBool_eq_true_iff w1 w2 w3 w4 s1 s2 s3 s4).mp hbparams with
    ⟨hw1, hw2, hw3, hw4, hs1, hs2, hs3, hs4⟩
  have hbpos : 0 < b.realPotential y := by
    exact b.realPotential_pos_of_mem_allBoxesValid hboxes hb hby
      hy0ne
      (by simpa [hs1] using hy1ne)
      (by simpa [hs2] using hy2ne)
      (by simpa [hs3] using hy3ne)
      (by simpa [hs4] using hy4ne)
  simpa [RatBox.realPotential, ratPotential, hw1, hw2, hw3, hw4, hs1, hs2, hs3, hs4] using hbpos

end

end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block355

def block355LeftL : Rat := ((9348502232142857181 : Rat) / 12500000000000000000)
def block355LeftR : Rat := ((7480756696428571459 : Rat) / 10000000000000000000)
def block355RightL : Rat := ((21848502232142857181 : Rat) / 12500000000000000000)
def block355RightR : Rat := ((27480756696428571459 : Rat) / 10000000000000000000)

def block355LeftBoxes : List RatBox := [
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((9348502232142857181 : Rat) / 12500000000000000000), R := ((7480756696428571459 : Rat) / 10000000000000000000), D0 := ((7480756696428571459 : Rat) / 10000000000000000000), D1 := ((13369936517857142819 : Rat) / 12500000000000000000), D2 := ((22625685267857142819 : Rat) / 12500000000000000000), D3 := ((95799615267857142729 : Rat) / 50000000000000000000), D4 := ((50612248749999997437 : Rat) / 25000000000000000000), LB := ((775722831806271 : Rat) / 125000000000000000) }
]

def block355LeftCertificate : Bool :=
  allBoxesValid block355LeftBoxes &&
  coversFromBool block355LeftBoxes block355LeftL block355LeftR

theorem block355LeftCertificate_eq_true :
    block355LeftCertificate = true := by
  native_decide

def block355RightChunk000 : List RatBox := [
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21848502232142857181 : Rat) / 12500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((869936517857142819 : Rat) / 12500000000000000000), D2 := ((10125685267857142819 : Rat) / 12500000000000000000), D3 := ((45799615267857142729 : Rat) / 50000000000000000000), D4 := ((25612248749999997437 : Rat) / 25000000000000000000), LB := ((3621995438302113 : Rat) / 2000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42319869196428571453 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((3836290700049097 : Rat) / 25000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23808371696428571453 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((9945139692261841 : Rat) / 100000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19180497321428571453 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((6399648920919057 : Rat) / 100000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16866560133928571453 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((799966713331357 : Rat) / 100000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14552622946428571453 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((969069759811117 : Rat) / 100000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13395654352678571453 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((14195852418652233 : Rat) / 1000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12817170055803571453 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((6484503955777349 : Rat) / 1000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12238685758928571453 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((5366893887403981 : Rat) / 500000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11949443610491071453 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((15525309764328421 : Rat) / 2000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11660201462053571453 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((5093391365012967 : Rat) / 1000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11370959313616071453 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((5477182363459343 : Rat) / 2000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11081717165178571453 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((89065653488523 : Rat) / 125000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10792475016741071453 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((536760784896697 : Rat) / 125000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10647853942522321453 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((1784348989217227 : Rat) / 500000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10503232868303571453 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((29368936768540133 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10358611794084821453 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((2401432754373517 : Rat) / 1000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10213990719866071453 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((2456606340658779 : Rat) / 1250000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10069369645647321453 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((2039566642386137 : Rat) / 1250000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9924748571428571453 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((14039985936009913 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9780127497209821453 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((12860699508832063 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9635506422991071453 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((12819384676914791 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9490885348772321453 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((436261542419783 : Rat) / 312500000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9346264274553571453 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((1020753886701517 : Rat) / 625000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9201643200334821453 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((999374872773337 : Rat) / 500000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9057022126116071453 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((249849794750881 : Rat) / 100000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8912401051897321453 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((784721236710223 : Rat) / 250000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8767779977678571453 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((3927040460258047 : Rat) / 1000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8623158903459821453 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((974180152025289 : Rat) / 200000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8478537829241071453 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((10159514547190829 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8189295680803571453 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((38025622991423313 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7900053532366071453 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((1846365191082673 : Rat) / 250000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7610811383928571453 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((222103380272759 : Rat) / 100000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7032327087053571453 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((7458705873049143 : Rat) / 500000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6453842790178571453 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((3226896069179347 : Rat) / 200000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516883874196428571453 : Rat) / 200000000000000000000), D0 := ((516883874196428571453 : Rat) / 200000000000000000000), D1 := ((153388854196428571453 : Rat) / 200000000000000000000), D2 := ((5296874196428571453 : Rat) / 200000000000000000000), D3 := ((5296874196428571453 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((1184003283208701 : Rat) / 100000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516883874196428571453 : Rat) / 200000000000000000000), R := ((1039064622589285714359 : Rat) / 400000000000000000000), D0 := ((1039064622589285714359 : Rat) / 400000000000000000000), D1 := ((312074582589285714359 : Rat) / 400000000000000000000), D2 := ((15890622589285714359 : Rat) / 400000000000000000000), D3 := ((15890622589285714359 : Rat) / 200000000000000000000), D4 := ((37590151517857122939 : Rat) / 200000000000000000000), LB := ((3366694208920301 : Rat) / 100000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1039064622589285714359 : Rat) / 400000000000000000000), R := ((261090374196428571453 : Rat) / 100000000000000000000), D0 := ((261090374196428571453 : Rat) / 100000000000000000000), D1 := ((79342864196428571453 : Rat) / 100000000000000000000), D2 := ((5296874196428571453 : Rat) / 100000000000000000000), D3 := ((5296874196428571453 : Rat) / 80000000000000000000), D4 := ((2795337153571426977 : Rat) / 16000000000000000000), LB := ((4672598767413657 : Rat) / 125000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261090374196428571453 : Rat) / 100000000000000000000), R := ((527477622589285714359 : Rat) / 200000000000000000000), D0 := ((527477622589285714359 : Rat) / 200000000000000000000), D1 := ((163982602589285714359 : Rat) / 200000000000000000000), D2 := ((15890622589285714359 : Rat) / 200000000000000000000), D3 := ((5296874196428571453 : Rat) / 100000000000000000000), D4 := ((16146638660714275743 : Rat) / 100000000000000000000), LB := ((4617323058324141 : Rat) / 200000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((527477622589285714359 : Rat) / 200000000000000000000), R := ((133193624196428571453 : Rat) / 50000000000000000000), D0 := ((133193624196428571453 : Rat) / 50000000000000000000), D1 := ((42319869196428571453 : Rat) / 50000000000000000000), D2 := ((5296874196428571453 : Rat) / 50000000000000000000), D3 := ((5296874196428571453 : Rat) / 200000000000000000000), D4 := ((26996403124999980033 : Rat) / 200000000000000000000), LB := ((2000309362065661 : Rat) / 20000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133193624196428571453 : Rat) / 50000000000000000000), R := ((268492328035714285827 : Rat) / 100000000000000000000), D0 := ((268492328035714285827 : Rat) / 100000000000000000000), D1 := ((86744818035714285827 : Rat) / 100000000000000000000), D2 := ((12698828035714285827 : Rat) / 100000000000000000000), D3 := ((2105079642857142921 : Rat) / 100000000000000000000), D4 := ((1084976446428570429 : Rat) / 10000000000000000000), LB := ((3158161214577837 : Rat) / 25000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((268492328035714285827 : Rat) / 100000000000000000000), R := ((67649351919642857187 : Rat) / 25000000000000000000), D0 := ((67649351919642857187 : Rat) / 25000000000000000000), D1 := ((22212474419642857187 : Rat) / 25000000000000000000), D2 := ((3700976919642857187 : Rat) / 25000000000000000000), D3 := ((2105079642857142921 : Rat) / 50000000000000000000), D4 := ((8744684821428561369 : Rat) / 100000000000000000000), LB := ((7699860289371807 : Rat) / 500000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((67649351919642857187 : Rat) / 25000000000000000000), R := ((543299895000000000417 : Rat) / 200000000000000000000), D0 := ((543299895000000000417 : Rat) / 200000000000000000000), D1 := ((179804875000000000417 : Rat) / 200000000000000000000), D2 := ((31712895000000000417 : Rat) / 200000000000000000000), D3 := ((2105079642857142921 : Rat) / 40000000000000000000), D4 := ((414975323660713653 : Rat) / 6250000000000000000), LB := ((23178042978346247 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((543299895000000000417 : Rat) / 200000000000000000000), R := ((217740973928571428751 : Rat) / 80000000000000000000), D0 := ((217740973928571428751 : Rat) / 80000000000000000000), D1 := ((72342965928571428751 : Rat) / 80000000000000000000), D2 := ((13106173928571428751 : Rat) / 80000000000000000000), D3 := ((23155876071428572131 : Rat) / 400000000000000000000), D4 := ((446965228571427759 : Rat) / 8000000000000000000), LB := ((638567472751439 : Rat) / 200000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((217740973928571428751 : Rat) / 80000000000000000000), R := ((2179514818928571430431 : Rat) / 800000000000000000000), D0 := ((2179514818928571430431 : Rat) / 800000000000000000000), D1 := ((725534738928571430431 : Rat) / 800000000000000000000), D2 := ((133166818928571430431 : Rat) / 800000000000000000000), D3 := ((48416831785714287183 : Rat) / 800000000000000000000), D4 := ((20243181785714245029 : Rat) / 400000000000000000000), LB := ((5894492489572023 : Rat) / 1000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2179514818928571430431 : Rat) / 800000000000000000000), R := ((272702487321428571669 : Rat) / 100000000000000000000), D0 := ((272702487321428571669 : Rat) / 100000000000000000000), D1 := ((90954977321428571669 : Rat) / 100000000000000000000), D2 := ((16908987321428571669 : Rat) / 100000000000000000000), D3 := ((6315238928571428763 : Rat) / 100000000000000000000), D4 := ((38381283928571347137 : Rat) / 800000000000000000000), LB := ((12944024049198477 : Rat) / 5000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272702487321428571669 : Rat) / 100000000000000000000), R := ((34922759014285714317 : Rat) / 12800000000000000000), D0 := ((34922759014285714317 : Rat) / 12800000000000000000), D1 := ((11659077734285714317 : Rat) / 12800000000000000000), D2 := ((2181191014285714317 : Rat) / 12800000000000000000), D3 := ((103148902500000003129 : Rat) / 1600000000000000000000), D4 := ((4534525535714275527 : Rat) / 100000000000000000000), LB := ((2580671939392959 : Rat) / 500000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((34922759014285714317 : Rat) / 12800000000000000000), R := ((2183724978214285716273 : Rat) / 800000000000000000000), D0 := ((2183724978214285716273 : Rat) / 800000000000000000000), D1 := ((729744898214285716273 : Rat) / 800000000000000000000), D2 := ((137376978214285716273 : Rat) / 800000000000000000000), D3 := ((2105079642857142921 : Rat) / 32000000000000000000), D4 := ((70447328928571265511 : Rat) / 1600000000000000000000), LB := ((4063610148250463 : Rat) / 1000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2183724978214285716273 : Rat) / 800000000000000000000), R := ((4369555036071428575467 : Rat) / 1600000000000000000000), D0 := ((4369555036071428575467 : Rat) / 1600000000000000000000), D1 := ((1461594876071428575467 : Rat) / 1600000000000000000000), D2 := ((276859036071428575467 : Rat) / 1600000000000000000000), D3 := ((107359061785714288971 : Rat) / 1600000000000000000000), D4 := ((6834224928571412259 : Rat) / 160000000000000000000), LB := ((98586346329501 : Rat) / 31250000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4369555036071428575467 : Rat) / 1600000000000000000000), R := ((1092915028928571429597 : Rat) / 400000000000000000000), D0 := ((1092915028928571429597 : Rat) / 400000000000000000000), D1 := ((365924988928571429597 : Rat) / 400000000000000000000), D2 := ((69741028928571429597 : Rat) / 400000000000000000000), D3 := ((27366035357142857973 : Rat) / 400000000000000000000), D4 := ((66237169642856979669 : Rat) / 1600000000000000000000), LB := ((24401678291584017 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1092915028928571429597 : Rat) / 400000000000000000000), R := ((4373765195357142861309 : Rat) / 1600000000000000000000), D0 := ((4373765195357142861309 : Rat) / 1600000000000000000000), D1 := ((1465805035357142861309 : Rat) / 1600000000000000000000), D2 := ((281069195357142861309 : Rat) / 1600000000000000000000), D3 := ((111569221071428574813 : Rat) / 1600000000000000000000), D4 := ((16033022499999959187 : Rat) / 400000000000000000000), LB := ((3852150264775811 : Rat) / 2000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4373765195357142861309 : Rat) / 1600000000000000000000), R := ((437587027500000000423 : Rat) / 160000000000000000000), D0 := ((437587027500000000423 : Rat) / 160000000000000000000), D1 := ((146791011500000000423 : Rat) / 160000000000000000000), D2 := ((28317427500000000423 : Rat) / 160000000000000000000), D3 := ((56837150357142858867 : Rat) / 800000000000000000000), D4 := ((62027010357142693827 : Rat) / 1600000000000000000000), LB := ((16197116201705497 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((437587027500000000423 : Rat) / 160000000000000000000), R := ((4377975354642857147151 : Rat) / 1600000000000000000000), D0 := ((4377975354642857147151 : Rat) / 1600000000000000000000), D1 := ((1470015194642857147151 : Rat) / 1600000000000000000000), D2 := ((285279354642857147151 : Rat) / 1600000000000000000000), D3 := ((23155876071428572131 : Rat) / 320000000000000000000), D4 := ((29960965357142775453 : Rat) / 800000000000000000000), LB := ((152938833195293 : Rat) / 100000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4377975354642857147151 : Rat) / 1600000000000000000000), R := ((547510054285714286259 : Rat) / 200000000000000000000), D0 := ((547510054285714286259 : Rat) / 200000000000000000000), D1 := ((184015034285714286259 : Rat) / 200000000000000000000), D2 := ((35923054285714286259 : Rat) / 200000000000000000000), D3 := ((14735557500000000447 : Rat) / 200000000000000000000), D4 := ((11563370214285681597 : Rat) / 320000000000000000000), LB := ((16646311077089249 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((547510054285714286259 : Rat) / 200000000000000000000), R := ((4382185513928571432993 : Rat) / 1600000000000000000000), D0 := ((4382185513928571432993 : Rat) / 1600000000000000000000), D1 := ((1474225353928571432993 : Rat) / 1600000000000000000000), D2 := ((289489513928571432993 : Rat) / 1600000000000000000000), D3 := ((119989539642857146497 : Rat) / 1600000000000000000000), D4 := ((6963971428571408133 : Rat) / 200000000000000000000), LB := ((509084359203979 : Rat) / 250000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4382185513928571432993 : Rat) / 1600000000000000000000), R := ((2192145296785714287957 : Rat) / 800000000000000000000), D0 := ((2192145296785714287957 : Rat) / 800000000000000000000), D1 := ((738165216785714287957 : Rat) / 800000000000000000000), D2 := ((145797296785714287957 : Rat) / 800000000000000000000), D3 := ((61047309642857144709 : Rat) / 800000000000000000000), D4 := ((53606691785714122143 : Rat) / 1600000000000000000000), LB := ((26569656401400077 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2192145296785714287957 : Rat) / 800000000000000000000), R := ((877279134642857143767 : Rat) / 320000000000000000000), D0 := ((877279134642857143767 : Rat) / 320000000000000000000), D1 := ((295687102642857143767 : Rat) / 320000000000000000000), D2 := ((58739934642857143767 : Rat) / 320000000000000000000), D3 := ((124199698928571432339 : Rat) / 1600000000000000000000), D4 := ((25750806071428489611 : Rat) / 800000000000000000000), LB := ((35407639374769873 : Rat) / 10000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((877279134642857143767 : Rat) / 320000000000000000000), R := ((1097125188214285715439 : Rat) / 400000000000000000000), D0 := ((1097125188214285715439 : Rat) / 400000000000000000000), D1 := ((370135148214285715439 : Rat) / 400000000000000000000), D2 := ((73951188214285715439 : Rat) / 400000000000000000000), D3 := ((6315238928571428763 : Rat) / 80000000000000000000), D4 := ((49396532499999836301 : Rat) / 1600000000000000000000), LB := ((1176012296894069 : Rat) / 250000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1097125188214285715439 : Rat) / 400000000000000000000), R := ((2196355456071428573799 : Rat) / 800000000000000000000), D0 := ((2196355456071428573799 : Rat) / 800000000000000000000), D1 := ((742375376071428573799 : Rat) / 800000000000000000000), D2 := ((150007456071428573799 : Rat) / 800000000000000000000), D3 := ((65257468928571430551 : Rat) / 800000000000000000000), D4 := ((2364572642857134669 : Rat) / 80000000000000000000), LB := ((8173673726866171 : Rat) / 5000000000000000000) },
  { w1 := ((89626313619803 : Rat) / 100000000000000), w2 := ((4749648757643457 : Rat) / 100000000000000000), w3 := ((751948885933783 : Rat) / 5000000000000000), w4 := ((1732793413009431 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133193624196428571453 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2196355456071428573799 : Rat) / 800000000000000000000), R := ((27480756696428571459 : Rat) / 10000000000000000000), D0 := ((27480756696428571459 : Rat) / 10000000000000000000), D1 := ((9306005696428571459 : Rat) / 10000000000000000000), D2 := ((1901406696428571459 : Rat) / 10000000000000000000), D3 := ((2105079642857142921 : Rat) / 25000000000000000000), D4 := ((21540646785714203769 : Rat) / 800000000000000000000), LB := ((5627680888649067 : Rat) / 1000000000000000000) }
]

def block355RightChunk000L : Rat := ((21848502232142857181 : Rat) / 12500000000000000000)
def block355RightChunk000R : Rat := ((27480756696428571459 : Rat) / 10000000000000000000)

def block355RightChunk000Certificate : Bool :=
  allBoxesValid block355RightChunk000 &&
  coversFromBool block355RightChunk000 block355RightChunk000L block355RightChunk000R

theorem block355RightChunk000Certificate_eq_true :
    block355RightChunk000Certificate = true := by
  native_decide

def block355RightChainCertificate : Bool :=
  decide (
    block355RightL = ((21848502232142857181 : Rat) / 12500000000000000000) /\
    ((27480756696428571459 : Rat) / 10000000000000000000) = block355RightR)

theorem block355RightChainCertificate_eq_true :
    block355RightChainCertificate = true := by
  native_decide

def block355LeftBoxCount : Nat := boxCount block355LeftBoxes
def block355RightBoxCount : Nat := 60

def block355_rational_certificate : Prop :=
    block355LeftCertificate = true /\
    block355RightChainCertificate = true /\
    block355RightChunk000Certificate = true

theorem block355_rational_certificate_proof :
    block355_rational_certificate := by
  exact ⟨block355LeftCertificate_eq_true, block355RightChainCertificate_eq_true, block355RightChunk000Certificate_eq_true⟩

end Block355
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block355

open Set

def block355W1 : Rat := ((89626313619803 : Rat) / 100000000000000)
def block355W2 : Rat := ((4749648757643457 : Rat) / 100000000000000000)
def block355W3 : Rat := ((751948885933783 : Rat) / 5000000000000000)
def block355W4 : Rat := ((1732793413009431 : Rat) / 12500000000000000)
def block355S1 : Rat := ((18174751 : Rat) / 10000000)
def block355S2 : Rat := ((511587 : Rat) / 200000)
def block355S3 : Rat := ((133193624196428571453 : Rat) / 50000000000000000000)
def block355S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block355V (y : ℝ) : ℝ :=
  ratPotential block355W1 block355W2 block355W3 block355W4 block355S1 block355S2 block355S3 block355S4 y

def block355LeftParamsCertificate : Bool :=
  allBoxesSameParams block355LeftBoxes block355W1 block355W2 block355W3 block355W4 block355S1 block355S2 block355S3 block355S4

theorem block355LeftParamsCertificate_eq_true :
    block355LeftParamsCertificate = true := by
  native_decide

theorem block355_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block355LeftL : ℝ) (block355LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block355S1 : ℝ))
    (hy2ne : y ≠ (block355S2 : ℝ))
    (hy3ne : y ≠ (block355S3 : ℝ))
    (hy4ne : y ≠ (block355S4 : ℝ)) :
    0 < block355V y := by
  have hcert := block355LeftCertificate_eq_true
  unfold block355LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block355LeftBoxes) (lo := block355LeftL) (hi := block355LeftR)
    (w1 := block355W1) (w2 := block355W2) (w3 := block355W3) (w4 := block355W4)
    (s1 := block355S1) (s2 := block355S2) (s3 := block355S3) (s4 := block355S4)
    hboxes hcover block355LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block355RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block355RightChunk000 block355W1 block355W2 block355W3 block355W4 block355S1 block355S2 block355S3 block355S4

theorem block355RightChunk000ParamsCertificate_eq_true :
    block355RightChunk000ParamsCertificate = true := by
  native_decide

theorem block355_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block355RightChunk000L : ℝ) (block355RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block355S1 : ℝ))
    (hy2ne : y ≠ (block355S2 : ℝ))
    (hy3ne : y ≠ (block355S3 : ℝ))
    (hy4ne : y ≠ (block355S4 : ℝ)) :
    0 < block355V y := by
  have hcert := block355RightChunk000Certificate_eq_true
  unfold block355RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block355RightChunk000) (lo := block355RightChunk000L) (hi := block355RightChunk000R)
    (w1 := block355W1) (w2 := block355W2) (w3 := block355W3) (w4 := block355W4)
    (s1 := block355S1) (s2 := block355S2) (s3 := block355S3) (s4 := block355S4)
    hboxes hcover block355RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block355_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block355RightL : ℝ) (block355RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block355S1 : ℝ))
    (hy2ne : y ≠ (block355S2 : ℝ))
    (hy3ne : y ≠ (block355S3 : ℝ))
    (hy4ne : y ≠ (block355S4 : ℝ)) :
    0 < block355V y := by
  have hL : (block355RightChunk000L : ℝ) = (block355RightL : ℝ) := by
    norm_num [block355RightChunk000L, block355RightL]
  have hR : (block355RightChunk000R : ℝ) = (block355RightR : ℝ) := by
    norm_num [block355RightChunk000R, block355RightR]
  have hyc : y ∈ Icc (block355RightChunk000L : ℝ) (block355RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block355_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block355_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block355LeftL : ℝ) (block355LeftR : ℝ) →
    y ≠ 0 → y ≠ (block355S1 : ℝ) → y ≠ (block355S2 : ℝ) →
    y ≠ (block355S3 : ℝ) → y ≠ (block355S4 : ℝ) → 0 < block355V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block355RightL : ℝ) (block355RightR : ℝ) →
    y ≠ 0 → y ≠ (block355S1 : ℝ) → y ≠ (block355S2 : ℝ) →
    y ≠ (block355S3 : ℝ) → y ≠ (block355S4 : ℝ) → 0 < block355V y)

theorem block355_reallog_certificate_proof :
    block355_reallog_certificate := by
  exact ⟨block355_left_V_pos, block355_right_V_pos⟩

end Block355
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block355.block355V
#check Erdos1038Lean.M1817475.Block355.block355_left_V_pos
#check Erdos1038Lean.M1817475.Block355.block355_right_V_pos
#check Erdos1038Lean.M1817475.Block355.block355_reallog_certificate_proof
