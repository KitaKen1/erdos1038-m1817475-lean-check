/-
Self-contained Lean4Web paste file.
Block 363 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block363

def block363LeftL : Rat := ((9328953125000000039 : Rat) / 12500000000000000000)
def block363LeftR : Rat := ((37325587053571428727 : Rat) / 50000000000000000000)
def block363RightL : Rat := ((21828953125000000039 : Rat) / 12500000000000000000)
def block363RightR : Rat := ((137325587053571428727 : Rat) / 50000000000000000000)

def block363LeftBoxes : List RatBox := [
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((9328953125000000039 : Rat) / 12500000000000000000), R := ((37325587053571428727 : Rat) / 50000000000000000000), D0 := ((37325587053571428727 : Rat) / 50000000000000000000), D1 := ((13389485624999999961 : Rat) / 12500000000000000000), D2 := ((22645234374999999961 : Rat) / 12500000000000000000), D3 := ((95721418839285714161 : Rat) / 50000000000000000000), D4 := ((50651346964285711721 : Rat) / 25000000000000000000), LB := ((6177434131562229 : Rat) / 1000000000000000000) }
]

def block363LeftCertificate : Bool :=
  allBoxesValid block363LeftBoxes &&
  coversFromBool block363LeftBoxes block363LeftL block363LeftR

theorem block363LeftCertificate_eq_true :
    block363LeftCertificate = true := by
  native_decide

def block363RightChunk000 : List RatBox := [
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21828953125000000039 : Rat) / 12500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((889485624999999961 : Rat) / 12500000000000000000), D2 := ((10145234374999999961 : Rat) / 12500000000000000000), D3 := ((45721418839285714161 : Rat) / 50000000000000000000), D4 := ((25651346964285711721 : Rat) / 25000000000000000000), LB := ((8751352525724039 : Rat) / 5000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42163476339285714317 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((1389991305281269 : Rat) / 10000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23651978839285714317 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((565150678969613 : Rat) / 6250000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19024104464285714317 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((5725184220611139 : Rat) / 100000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16710167276785714317 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((31055493112302907 : Rat) / 10000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14396230089285714317 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((1206317716806049 : Rat) / 200000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13239261495535714317 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((2239035747068907 : Rat) / 200000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12660777198660714317 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((318099989359657 : Rat) / 80000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12082292901785714317 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((8577676345920493 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11793050753348214317 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((5860340297859951 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11503808604910714317 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((34471370771655407 : Rat) / 10000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11214566456473214317 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((13509188646957937 : Rat) / 10000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10925324308035714317 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((18820447537841 : Rat) / 3906250000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10780703233816964317 : Rat) / 50000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((161806820497441 : Rat) / 40000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10636082159598214317 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((3361739522862811 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10491461085379464317 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((1385089092349051 : Rat) / 500000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10346840011160714317 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((5682746500564259 : Rat) / 2500000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10202218936941964317 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((18733057013874121 : Rat) / 10000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10057597862723214317 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((1573816928772953 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9912976788504464317 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((13778846898912511 : Rat) / 10000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9768355714285714317 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((6445110477377447 : Rat) / 5000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9623734640066964317 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((409697681866281 : Rat) / 312500000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9479113565848214317 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((7240220831464389 : Rat) / 5000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9334492491629464317 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((1065343283797697 : Rat) / 625000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9189871417410714317 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((834180458708611 : Rat) / 400000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9045250343191964317 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((1038447472772841 : Rat) / 400000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8900629268973214317 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((405306352138899 : Rat) / 125000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8756008194754464317 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((4030953461437559 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8611387120535714317 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((1823358890641613 : Rat) / 50000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8322144972098214317 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((4856151247329521 : Rat) / 2000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8032902823660714317 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((5526136012166533 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7743660675223214317 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((942864322709483 : Rat) / 100000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7454418526785714317 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((1180051682917481 : Rat) / 250000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6875934229910714317 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1810169464180869 : Rat) / 100000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6297449933035714317 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((507307401473063 : Rat) / 25000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516727481339285714317 : Rat) / 200000000000000000000), D0 := ((516727481339285714317 : Rat) / 200000000000000000000), D1 := ((153232461339285714317 : Rat) / 200000000000000000000), D2 := ((5140481339285714317 : Rat) / 200000000000000000000), D3 := ((5140481339285714317 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((10263084323375221 : Rat) / 500000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516727481339285714317 : Rat) / 200000000000000000000), R := ((260933981339285714317 : Rat) / 100000000000000000000), D0 := ((260933981339285714317 : Rat) / 100000000000000000000), D1 := ((79186471339285714317 : Rat) / 100000000000000000000), D2 := ((5140481339285714317 : Rat) / 100000000000000000000), D3 := ((15421444017857142951 : Rat) / 200000000000000000000), D4 := ((1509861774999999203 : Rat) / 8000000000000000000), LB := ((10436132838371137 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((260933981339285714317 : Rat) / 100000000000000000000), R := ((527008444017857142951 : Rat) / 200000000000000000000), D0 := ((527008444017857142951 : Rat) / 200000000000000000000), D1 := ((163513424017857142951 : Rat) / 200000000000000000000), D2 := ((15421444017857142951 : Rat) / 200000000000000000000), D3 := ((5140481339285714317 : Rat) / 100000000000000000000), D4 := ((16303031517857132879 : Rat) / 100000000000000000000), LB := ((3558416812282017 : Rat) / 100000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((527008444017857142951 : Rat) / 200000000000000000000), R := ((133037231339285714317 : Rat) / 50000000000000000000), D0 := ((133037231339285714317 : Rat) / 50000000000000000000), D1 := ((42163476339285714317 : Rat) / 50000000000000000000), D2 := ((5140481339285714317 : Rat) / 50000000000000000000), D3 := ((5140481339285714317 : Rat) / 200000000000000000000), D4 := ((27465581696428551441 : Rat) / 200000000000000000000), LB := ((573497087405091 : Rat) / 5000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133037231339285714317 : Rat) / 50000000000000000000), R := ((268218640535714285839 : Rat) / 100000000000000000000), D0 := ((268218640535714285839 : Rat) / 100000000000000000000), D1 := ((86471130535714285839 : Rat) / 100000000000000000000), D2 := ((12425140535714285839 : Rat) / 100000000000000000000), D3 := ((428835571428571441 : Rat) / 20000000000000000000), D4 := ((5581275089285709281 : Rat) / 50000000000000000000), LB := ((330287367456589 : Rat) / 2500000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((268218640535714285839 : Rat) / 100000000000000000000), R := ((67590704598214285761 : Rat) / 25000000000000000000), D0 := ((67590704598214285761 : Rat) / 25000000000000000000), D1 := ((22153827098214285761 : Rat) / 25000000000000000000), D2 := ((3642329598214285761 : Rat) / 25000000000000000000), D3 := ((428835571428571441 : Rat) / 10000000000000000000), D4 := ((9018372321428561357 : Rat) / 100000000000000000000), LB := ((18929832871730223 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((67590704598214285761 : Rat) / 25000000000000000000), R := ((542869814642857143293 : Rat) / 200000000000000000000), D0 := ((542869814642857143293 : Rat) / 200000000000000000000), D1 := ((179374794642857143293 : Rat) / 200000000000000000000), D2 := ((31282814642857143293 : Rat) / 200000000000000000000), D3 := ((428835571428571441 : Rat) / 8000000000000000000), D4 := ((859274308035713019 : Rat) / 12500000000000000000), LB := ((4763093047737199 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((542869814642857143293 : Rat) / 200000000000000000000), R := ((1087883807142857143791 : Rat) / 400000000000000000000), D0 := ((1087883807142857143791 : Rat) / 400000000000000000000), D1 := ((360893767142857143791 : Rat) / 400000000000000000000), D2 := ((64709807142857143791 : Rat) / 400000000000000000000), D3 := ((4717191285714285851 : Rat) / 80000000000000000000), D4 := ((11604211071428551099 : Rat) / 200000000000000000000), LB := ((5009564421430357 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1087883807142857143791 : Rat) / 400000000000000000000), R := ((2177911792142857144787 : Rat) / 800000000000000000000), D0 := ((2177911792142857144787 : Rat) / 800000000000000000000), D1 := ((723931712142857144787 : Rat) / 800000000000000000000), D2 := ((131563792142857144787 : Rat) / 800000000000000000000), D3 := ((9863218142857143143 : Rat) / 160000000000000000000), D4 := ((21064244285714244993 : Rat) / 400000000000000000000), LB := ((7348418375793253 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2177911792142857144787 : Rat) / 800000000000000000000), R := ((272506996250000000249 : Rat) / 100000000000000000000), D0 := ((272506996250000000249 : Rat) / 100000000000000000000), D1 := ((90759486250000000249 : Rat) / 100000000000000000000), D2 := ((16713496250000000249 : Rat) / 100000000000000000000), D3 := ((1286506714285714323 : Rat) / 20000000000000000000), D4 := ((39984310714285632781 : Rat) / 800000000000000000000), LB := ((37718254886127123 : Rat) / 10000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272506996250000000249 : Rat) / 100000000000000000000), R := ((2182200147857142859197 : Rat) / 800000000000000000000), D0 := ((2182200147857142859197 : Rat) / 800000000000000000000), D1 := ((728220067857142859197 : Rat) / 800000000000000000000), D2 := ((135852147857142859197 : Rat) / 800000000000000000000), D3 := ((428835571428571441 : Rat) / 6400000000000000000), D4 := ((4730016607142846947 : Rat) / 100000000000000000000), LB := ((4412025871330383 : Rat) / 5000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2182200147857142859197 : Rat) / 800000000000000000000), R := ((4366544473571428575599 : Rat) / 1600000000000000000000), D0 := ((4366544473571428575599 : Rat) / 1600000000000000000000), D1 := ((1458584313571428575599 : Rat) / 1600000000000000000000), D2 := ((273848473571428575599 : Rat) / 1600000000000000000000), D3 := ((21870614142857143491 : Rat) / 320000000000000000000), D4 := ((35695954999999918371 : Rat) / 800000000000000000000), LB := ((3824234312220287 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4366544473571428575599 : Rat) / 1600000000000000000000), R := ((1092172162857142858201 : Rat) / 400000000000000000000), D0 := ((1092172162857142858201 : Rat) / 400000000000000000000), D1 := ((365182122857142858201 : Rat) / 400000000000000000000), D2 := ((68998162857142858201 : Rat) / 400000000000000000000), D3 := ((5574862428571428733 : Rat) / 80000000000000000000), D4 := ((69247732142856979537 : Rat) / 1600000000000000000000), LB := ((3690858971733893 : Rat) / 1250000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1092172162857142858201 : Rat) / 400000000000000000000), R := ((4370832829285714290009 : Rat) / 1600000000000000000000), D0 := ((4370832829285714290009 : Rat) / 1600000000000000000000), D1 := ((1462872669285714290009 : Rat) / 1600000000000000000000), D2 := ((278136829285714290009 : Rat) / 1600000000000000000000), D3 := ((22728285285714286373 : Rat) / 320000000000000000000), D4 := ((16775888571428530583 : Rat) / 400000000000000000000), LB := ((4552393511836339 : Rat) / 2000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4370832829285714290009 : Rat) / 1600000000000000000000), R := ((2186488503571428573607 : Rat) / 800000000000000000000), D0 := ((2186488503571428573607 : Rat) / 800000000000000000000), D1 := ((732508423571428573607 : Rat) / 800000000000000000000), D2 := ((140140503571428573607 : Rat) / 800000000000000000000), D3 := ((11578560428571428907 : Rat) / 160000000000000000000), D4 := ((64959376428571265127 : Rat) / 1600000000000000000000), LB := ((900640218939347 : Rat) / 500000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2186488503571428573607 : Rat) / 800000000000000000000), R := ((4375121185000000004419 : Rat) / 1600000000000000000000), D0 := ((4375121185000000004419 : Rat) / 1600000000000000000000), D1 := ((1467161025000000004419 : Rat) / 1600000000000000000000), D2 := ((282425185000000004419 : Rat) / 1600000000000000000000), D3 := ((4717191285714285851 : Rat) / 64000000000000000000), D4 := ((31407599285714203961 : Rat) / 800000000000000000000), LB := ((3070893898377891 : Rat) / 2000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4375121185000000004419 : Rat) / 1600000000000000000000), R := ((547158170357142857703 : Rat) / 200000000000000000000), D0 := ((547158170357142857703 : Rat) / 200000000000000000000), D1 := ((183663150357142857703 : Rat) / 200000000000000000000), D2 := ((35571170357142857703 : Rat) / 200000000000000000000), D3 := ((3001849000000000087 : Rat) / 40000000000000000000), D4 := ((60671020714285550717 : Rat) / 1600000000000000000000), LB := ((14873094194982617 : Rat) / 10000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((547158170357142857703 : Rat) / 200000000000000000000), R := ((4379409540714285718829 : Rat) / 1600000000000000000000), D0 := ((4379409540714285718829 : Rat) / 1600000000000000000000), D1 := ((1471449380714285718829 : Rat) / 1600000000000000000000), D2 := ((286713540714285718829 : Rat) / 1600000000000000000000), D3 := ((24443627571428572137 : Rat) / 320000000000000000000), D4 := ((7315855357142836689 : Rat) / 200000000000000000000), LB := ((1666721057254017 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4379409540714285718829 : Rat) / 1600000000000000000000), R := ((2190776859285714288017 : Rat) / 800000000000000000000), D0 := ((2190776859285714288017 : Rat) / 800000000000000000000), D1 := ((736796779285714288017 : Rat) / 800000000000000000000), D2 := ((144428859285714288017 : Rat) / 800000000000000000000), D3 := ((12436231571428571789 : Rat) / 160000000000000000000), D4 := ((56382664999999836307 : Rat) / 1600000000000000000000), LB := ((2084938253844759 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2190776859285714288017 : Rat) / 800000000000000000000), R := ((4383697896428571433239 : Rat) / 1600000000000000000000), D0 := ((4383697896428571433239 : Rat) / 1600000000000000000000), D1 := ((1475737736428571433239 : Rat) / 1600000000000000000000), D2 := ((291001896428571433239 : Rat) / 1600000000000000000000), D3 := ((25301298714285715019 : Rat) / 320000000000000000000), D4 := ((27119243571428489551 : Rat) / 800000000000000000000), LB := ((2754817278640853 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4383697896428571433239 : Rat) / 1600000000000000000000), R := ((1096460518571428572611 : Rat) / 400000000000000000000), D0 := ((1096460518571428572611 : Rat) / 400000000000000000000), D1 := ((369470478571428572611 : Rat) / 400000000000000000000), D2 := ((73286518571428572611 : Rat) / 400000000000000000000), D3 := ((1286506714285714323 : Rat) / 16000000000000000000), D4 := ((52094309285714121897 : Rat) / 1600000000000000000000), LB := ((3691052494945557 : Rat) / 1000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1096460518571428572611 : Rat) / 400000000000000000000), R := ((2195065215000000002427 : Rat) / 800000000000000000000), D0 := ((2195065215000000002427 : Rat) / 800000000000000000000), D1 := ((741085135000000002427 : Rat) / 800000000000000000000), D2 := ((148717215000000002427 : Rat) / 800000000000000000000), D3 := ((13293902714285714671 : Rat) / 160000000000000000000), D4 := ((12487532857142816173 : Rat) / 400000000000000000000), LB := ((3218521792560103 : Rat) / 10000000000000000000) },
  { w1 := ((8807792774182291 : Rat) / 10000000000000000), w2 := ((11840020660607839 : Rat) / 250000000000000000), w3 := ((15266026736777283 : Rat) / 100000000000000000), w4 := ((13927109568961873 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133037231339285714317 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2195065215000000002427 : Rat) / 800000000000000000000), R := ((137325587053571428727 : Rat) / 50000000000000000000), D0 := ((137325587053571428727 : Rat) / 50000000000000000000), D1 := ((46451832053571428727 : Rat) / 50000000000000000000), D2 := ((9428837053571428727 : Rat) / 50000000000000000000), D3 := ((428835571428571441 : Rat) / 5000000000000000000), D4 := ((22830887857142775141 : Rat) / 800000000000000000000), LB := ((18887970766902351 : Rat) / 5000000000000000000) }
]

def block363RightChunk000L : Rat := ((21828953125000000039 : Rat) / 12500000000000000000)
def block363RightChunk000R : Rat := ((137325587053571428727 : Rat) / 50000000000000000000)

def block363RightChunk000Certificate : Bool :=
  allBoxesValid block363RightChunk000 &&
  coversFromBool block363RightChunk000 block363RightChunk000L block363RightChunk000R

theorem block363RightChunk000Certificate_eq_true :
    block363RightChunk000Certificate = true := by
  native_decide

def block363RightChainCertificate : Bool :=
  decide (
    block363RightL = ((21828953125000000039 : Rat) / 12500000000000000000) /\
    ((137325587053571428727 : Rat) / 50000000000000000000) = block363RightR)

theorem block363RightChainCertificate_eq_true :
    block363RightChainCertificate = true := by
  native_decide

def block363LeftBoxCount : Nat := boxCount block363LeftBoxes
def block363RightBoxCount : Nat := 58

def block363_rational_certificate : Prop :=
    block363LeftCertificate = true /\
    block363RightChainCertificate = true /\
    block363RightChunk000Certificate = true

theorem block363_rational_certificate_proof :
    block363_rational_certificate := by
  exact ⟨block363LeftCertificate_eq_true, block363RightChainCertificate_eq_true, block363RightChunk000Certificate_eq_true⟩

end Block363
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block363

open Set

def block363W1 : Rat := ((8807792774182291 : Rat) / 10000000000000000)
def block363W2 : Rat := ((11840020660607839 : Rat) / 250000000000000000)
def block363W3 : Rat := ((15266026736777283 : Rat) / 100000000000000000)
def block363W4 : Rat := ((13927109568961873 : Rat) / 100000000000000000)
def block363S1 : Rat := ((18174751 : Rat) / 10000000)
def block363S2 : Rat := ((511587 : Rat) / 200000)
def block363S3 : Rat := ((133037231339285714317 : Rat) / 50000000000000000000)
def block363S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block363V (y : ℝ) : ℝ :=
  ratPotential block363W1 block363W2 block363W3 block363W4 block363S1 block363S2 block363S3 block363S4 y

def block363LeftParamsCertificate : Bool :=
  allBoxesSameParams block363LeftBoxes block363W1 block363W2 block363W3 block363W4 block363S1 block363S2 block363S3 block363S4

theorem block363LeftParamsCertificate_eq_true :
    block363LeftParamsCertificate = true := by
  native_decide

theorem block363_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block363LeftL : ℝ) (block363LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block363S1 : ℝ))
    (hy2ne : y ≠ (block363S2 : ℝ))
    (hy3ne : y ≠ (block363S3 : ℝ))
    (hy4ne : y ≠ (block363S4 : ℝ)) :
    0 < block363V y := by
  have hcert := block363LeftCertificate_eq_true
  unfold block363LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block363LeftBoxes) (lo := block363LeftL) (hi := block363LeftR)
    (w1 := block363W1) (w2 := block363W2) (w3 := block363W3) (w4 := block363W4)
    (s1 := block363S1) (s2 := block363S2) (s3 := block363S3) (s4 := block363S4)
    hboxes hcover block363LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block363RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block363RightChunk000 block363W1 block363W2 block363W3 block363W4 block363S1 block363S2 block363S3 block363S4

theorem block363RightChunk000ParamsCertificate_eq_true :
    block363RightChunk000ParamsCertificate = true := by
  native_decide

theorem block363_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block363RightChunk000L : ℝ) (block363RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block363S1 : ℝ))
    (hy2ne : y ≠ (block363S2 : ℝ))
    (hy3ne : y ≠ (block363S3 : ℝ))
    (hy4ne : y ≠ (block363S4 : ℝ)) :
    0 < block363V y := by
  have hcert := block363RightChunk000Certificate_eq_true
  unfold block363RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block363RightChunk000) (lo := block363RightChunk000L) (hi := block363RightChunk000R)
    (w1 := block363W1) (w2 := block363W2) (w3 := block363W3) (w4 := block363W4)
    (s1 := block363S1) (s2 := block363S2) (s3 := block363S3) (s4 := block363S4)
    hboxes hcover block363RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block363_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block363RightL : ℝ) (block363RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block363S1 : ℝ))
    (hy2ne : y ≠ (block363S2 : ℝ))
    (hy3ne : y ≠ (block363S3 : ℝ))
    (hy4ne : y ≠ (block363S4 : ℝ)) :
    0 < block363V y := by
  have hL : (block363RightChunk000L : ℝ) = (block363RightL : ℝ) := by
    norm_num [block363RightChunk000L, block363RightL]
  have hR : (block363RightChunk000R : ℝ) = (block363RightR : ℝ) := by
    norm_num [block363RightChunk000R, block363RightR]
  have hyc : y ∈ Icc (block363RightChunk000L : ℝ) (block363RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block363_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block363_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block363LeftL : ℝ) (block363LeftR : ℝ) →
    y ≠ 0 → y ≠ (block363S1 : ℝ) → y ≠ (block363S2 : ℝ) →
    y ≠ (block363S3 : ℝ) → y ≠ (block363S4 : ℝ) → 0 < block363V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block363RightL : ℝ) (block363RightR : ℝ) →
    y ≠ 0 → y ≠ (block363S1 : ℝ) → y ≠ (block363S2 : ℝ) →
    y ≠ (block363S3 : ℝ) → y ≠ (block363S4 : ℝ) → 0 < block363V y)

theorem block363_reallog_certificate_proof :
    block363_reallog_certificate := by
  exact ⟨block363_left_V_pos, block363_right_V_pos⟩

end Block363
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block363.block363V
#check Erdos1038Lean.M1817475.Block363.block363_left_V_pos
#check Erdos1038Lean.M1817475.Block363.block363_right_V_pos
#check Erdos1038Lean.M1817475.Block363.block363_reallog_certificate_proof
