/-
Self-contained Lean4Web paste file.
Block 393 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block393

def block393LeftL : Rat := ((18511287946428571513 : Rat) / 25000000000000000000)
def block393LeftR : Rat := ((37032350446428571597 : Rat) / 50000000000000000000)
def block393RightL : Rat := ((43511287946428571513 : Rat) / 25000000000000000000)
def block393RightR : Rat := ((137032350446428571597 : Rat) / 50000000000000000000)

def block393LeftBoxes : List RatBox := [
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((18511287946428571513 : Rat) / 25000000000000000000), R := ((37032350446428571597 : Rat) / 50000000000000000000), D0 := ((37032350446428571597 : Rat) / 50000000000000000000), D1 := ((26925589553571428487 : Rat) / 25000000000000000000), D2 := ((45437087053571428487 : Rat) / 25000000000000000000), D3 := ((95428182232142857031 : Rat) / 50000000000000000000), D4 := ((51042329107142854561 : Rat) / 25000000000000000000), LB := ((1729172058535261 : Rat) / 2000000000000000000) }
]

def block393LeftCertificate : Bool :=
  allBoxesValid block393LeftBoxes &&
  coversFromBool block393LeftBoxes block393LeftL block393LeftR

theorem block393LeftCertificate_eq_true :
    block393LeftCertificate = true := by
  native_decide

def block393RightChunk000 : List RatBox := [
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((43511287946428571513 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1925589553571428487 : Rat) / 25000000000000000000), D2 := ((20437087053571428487 : Rat) / 25000000000000000000), D3 := ((45428182232142857031 : Rat) / 50000000000000000000), D4 := ((26042329107142854561 : Rat) / 25000000000000000000), LB := ((14773264060680773 : Rat) / 10000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41577003125000000057 : Rat) / 50000000000000000000), D4 := ((12058369776785713037 : Rat) / 12500000000000000000), LB := ((3165639865213423 : Rat) / 50000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23065505625000000057 : Rat) / 50000000000000000000), D4 := ((7430495401785713037 : Rat) / 12500000000000000000), LB := ((4335054631078267 : Rat) / 100000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18437631250000000057 : Rat) / 50000000000000000000), D4 := ((6273526808035713037 : Rat) / 12500000000000000000), LB := ((1091890980410267 : Rat) / 50000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16123694062500000057 : Rat) / 50000000000000000000), D4 := ((5695042511160713037 : Rat) / 12500000000000000000), LB := ((419035910167643 : Rat) / 20000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((14966725468750000057 : Rat) / 50000000000000000000), D4 := ((5405800362723213037 : Rat) / 12500000000000000000), LB := ((219249140083767 : Rat) / 125000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13809756875000000057 : Rat) / 50000000000000000000), D4 := ((5116558214285713037 : Rat) / 12500000000000000000), LB := ((7045820033802441 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((13231272578125000057 : Rat) / 50000000000000000000), D4 := ((4971937140066963037 : Rat) / 12500000000000000000), LB := ((1936099234634281 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((766707007 : Rat) / 320000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12652788281250000057 : Rat) / 50000000000000000000), D4 := ((4827316065848213037 : Rat) / 12500000000000000000), LB := ((185109039566973 : Rat) / 40000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((12363546132812500057 : Rat) / 50000000000000000000), D4 := ((4755005528738838037 : Rat) / 12500000000000000000), LB := ((19916624122480187 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12074303984375000057 : Rat) / 50000000000000000000), D4 := ((4682694991629463037 : Rat) / 12500000000000000000), LB := ((4724435182902803 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((11929682910156250057 : Rat) / 50000000000000000000), D4 := ((4646539723074775537 : Rat) / 12500000000000000000), LB := ((36223291440797 : Rat) / 10000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((123561673 : Rat) / 51200000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11785061835937500057 : Rat) / 50000000000000000000), D4 := ((4610384454520088037 : Rat) / 12500000000000000000), LB := ((12952136112553553 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((11640440761718750057 : Rat) / 50000000000000000000), D4 := ((4574229185965400537 : Rat) / 12500000000000000000), LB := ((651977430807249 : Rat) / 400000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((387055803 : Rat) / 160000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11495819687500000057 : Rat) / 50000000000000000000), D4 := ((4538073917410713037 : Rat) / 12500000000000000000), LB := ((7421610843374171 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((12407999493 : Rat) / 5120000000), D0 := ((12407999493 : Rat) / 5120000000), D1 := ((3102526981 : Rat) / 5120000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((11351198613281250057 : Rat) / 50000000000000000000), D4 := ((4501918648856025537 : Rat) / 12500000000000000000), LB := ((6091914139954649 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12407999493 : Rat) / 5120000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((688627707 : Rat) / 5120000000), D3 := ((11278888076171875057 : Rat) / 50000000000000000000), D4 := ((4483841014578681787 : Rat) / 12500000000000000000), LB := ((10266087661660317 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11206577539062500057 : Rat) / 50000000000000000000), D4 := ((4465763380301338037 : Rat) / 12500000000000000000), LB := ((1688750045334031 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((11134267001953125057 : Rat) / 50000000000000000000), D4 := ((4447685746023994287 : Rat) / 12500000000000000000), LB := ((1343555472495317 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((11061956464843750057 : Rat) / 50000000000000000000), D4 := ((4429608111746650537 : Rat) / 12500000000000000000), LB := ((10178316998140091 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((10989645927734375057 : Rat) / 50000000000000000000), D4 := ((4411530477469306787 : Rat) / 12500000000000000000), LB := ((1779456061032289 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((81450589 : Rat) / 640000000), D3 := ((10917335390625000057 : Rat) / 50000000000000000000), D4 := ((4393452843191963037 : Rat) / 12500000000000000000), LB := ((10640434186801051 : Rat) / 25000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((10845024853515625057 : Rat) / 50000000000000000000), D4 := ((4375375208914619287 : Rat) / 12500000000000000000), LB := ((15955249812885097 : Rat) / 100000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((24927067971 : Rat) / 10240000000), D0 := ((24927067971 : Rat) / 10240000000), D1 := ((6316122947 : Rat) / 10240000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10772714316406250057 : Rat) / 50000000000000000000), D4 := ((4357297574637275537 : Rat) / 12500000000000000000), LB := ((11504509715571931 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24927067971 : Rat) / 10240000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((1266186429 : Rat) / 10240000000), D3 := ((10736559047851562557 : Rat) / 50000000000000000000), D4 := ((2174129378749301831 : Rat) / 6250000000000000000), LB := ((2068168759575717 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((24941877169 : Rat) / 10240000000), D0 := ((24941877169 : Rat) / 10240000000), D1 := ((1266186429 : Rat) / 2048000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((10700403779296875057 : Rat) / 50000000000000000000), D4 := ((4339219940359931787 : Rat) / 12500000000000000000), LB := ((1845775110493053 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24941877169 : Rat) / 10240000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((1251377231 : Rat) / 10240000000), D3 := ((10664248510742187557 : Rat) / 50000000000000000000), D4 := ((541272640402657489 : Rat) / 1562500000000000000), LB := ((8168902315712767 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((24956686367 : Rat) / 10240000000), D0 := ((24956686367 : Rat) / 10240000000), D1 := ((6345741343 : Rat) / 10240000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10628093242187500057 : Rat) / 50000000000000000000), D4 := ((4321142306082588037 : Rat) / 12500000000000000000), LB := ((57289807726979 : Rat) / 80000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24956686367 : Rat) / 10240000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((1236568033 : Rat) / 10240000000), D3 := ((10591937973632812557 : Rat) / 50000000000000000000), D4 := ((2156051744471958081 : Rat) / 6250000000000000000), LB := ((3103076506313779 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((4994299113 : Rat) / 2048000000), D0 := ((4994299113 : Rat) / 2048000000), D1 := ((6360550541 : Rat) / 10240000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((10555782705078125057 : Rat) / 50000000000000000000), D4 := ((4303064671805244287 : Rat) / 12500000000000000000), LB := ((5303994689018487 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4994299113 : Rat) / 2048000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((244351767 : Rat) / 2048000000), D3 := ((10519627436523437557 : Rat) / 50000000000000000000), D4 := ((1073506463666643103 : Rat) / 3125000000000000000), LB := ((891013409191399 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((24986304763 : Rat) / 10240000000), D0 := ((24986304763 : Rat) / 10240000000), D1 := ((6375359739 : Rat) / 10240000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10483472167968750057 : Rat) / 50000000000000000000), D4 := ((4284987037527900537 : Rat) / 12500000000000000000), LB := ((914922762333889 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24986304763 : Rat) / 10240000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((1206949637 : Rat) / 10240000000), D3 := ((10447316899414062557 : Rat) / 50000000000000000000), D4 := ((2137974110194614331 : Rat) / 6250000000000000000), LB := ((2918192679806919 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((25001113961 : Rat) / 10240000000), D0 := ((25001113961 : Rat) / 10240000000), D1 := ((6390168937 : Rat) / 10240000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((10411161630859375057 : Rat) / 50000000000000000000), D4 := ((4266909403250556787 : Rat) / 12500000000000000000), LB := ((5577257588476603 : Rat) / 25000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25001113961 : Rat) / 10240000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((1192140439 : Rat) / 10240000000), D3 := ((10375006362304687557 : Rat) / 50000000000000000000), D4 := ((266116911631992807 : Rat) / 781250000000000000), LB := ((1598158436940389 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((156303241 : Rat) / 64000000), R := ((25015923159 : Rat) / 10240000000), D0 := ((25015923159 : Rat) / 10240000000), D1 := ((1280995627 : Rat) / 2048000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10338851093750000057 : Rat) / 50000000000000000000), D4 := ((4248831768973213037 : Rat) / 12500000000000000000), LB := ((5101502683252379 : Rat) / 50000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25015923159 : Rat) / 10240000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((1177331241 : Rat) / 10240000000), D3 := ((10302695825195312557 : Rat) / 50000000000000000000), D4 := ((2119896475917270581 : Rat) / 6250000000000000000), LB := ((4976764295930303 : Rat) / 100000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((25030732357 : Rat) / 10240000000), D0 := ((25030732357 : Rat) / 10240000000), D1 := ((6419787333 : Rat) / 10240000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((10266540556640625057 : Rat) / 50000000000000000000), D4 := ((4230754134695869287 : Rat) / 12500000000000000000), LB := ((7659692130776441 : Rat) / 2500000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25030732357 : Rat) / 10240000000), R := ((50068869313 : Rat) / 20480000000), D0 := ((50068869313 : Rat) / 20480000000), D1 := ((2569395853 : Rat) / 4096000000), D2 := ((1162522043 : Rat) / 10240000000), D3 := ((10230385288085937557 : Rat) / 50000000000000000000), D4 := ((1055428829389299353 : Rat) / 3125000000000000000), LB := ((5719337972334981 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50068869313 : Rat) / 20480000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((2317639487 : Rat) / 20480000000), D3 := ((10212307653808593807 : Rat) / 50000000000000000000), D4 := ((8434391817975722949 : Rat) / 25000000000000000000), LB := ((5532004623443609 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((50083678511 : Rat) / 20480000000), D0 := ((50083678511 : Rat) / 20480000000), D1 := ((12861788463 : Rat) / 20480000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10194230019531250057 : Rat) / 50000000000000000000), D4 := ((4212676500418525537 : Rat) / 12500000000000000000), LB := ((1071759520580029 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50083678511 : Rat) / 20480000000), R := ((5009108311 : Rat) / 2048000000), D0 := ((5009108311 : Rat) / 2048000000), D1 := ((6434596531 : Rat) / 10240000000), D2 := ((2302830289 : Rat) / 20480000000), D3 := ((10176152385253906307 : Rat) / 50000000000000000000), D4 := ((8416314183698379199 : Rat) / 25000000000000000000), LB := ((2599881673741311 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5009108311 : Rat) / 2048000000), R := ((50098487709 : Rat) / 20480000000), D0 := ((50098487709 : Rat) / 20480000000), D1 := ((12876597661 : Rat) / 20480000000), D2 := ((229542569 : Rat) / 2048000000), D3 := ((10158074750976562557 : Rat) / 50000000000000000000), D4 := ((2101818841639926831 : Rat) / 6250000000000000000), LB := ((5054948672166271 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50098487709 : Rat) / 20480000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((2288021091 : Rat) / 20480000000), D3 := ((10139997116699218807 : Rat) / 50000000000000000000), D4 := ((8398236549421035449 : Rat) / 25000000000000000000), LB := ((4924400774222459 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((50113296907 : Rat) / 20480000000), D0 := ((50113296907 : Rat) / 20480000000), D1 := ((12891406859 : Rat) / 20480000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((10121919482421875057 : Rat) / 50000000000000000000), D4 := ((4194598866141181787 : Rat) / 12500000000000000000), LB := ((9616334474800703 : Rat) / 20000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50113296907 : Rat) / 20480000000), R := ((25060350753 : Rat) / 10240000000), D0 := ((25060350753 : Rat) / 10240000000), D1 := ((6449405729 : Rat) / 10240000000), D2 := ((2273211893 : Rat) / 20480000000), D3 := ((10103841848144531307 : Rat) / 50000000000000000000), D4 := ((8380158915143691699 : Rat) / 25000000000000000000), LB := ((47062960361751727 : Rat) / 100000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25060350753 : Rat) / 10240000000), R := ((10025621221 : Rat) / 4096000000), D0 := ((10025621221 : Rat) / 4096000000), D1 := ((12906216057 : Rat) / 20480000000), D2 := ((1132903647 : Rat) / 10240000000), D3 := ((10085764213867187557 : Rat) / 50000000000000000000), D4 := ((523195006125313739 : Rat) / 1562500000000000000), LB := ((4618835540030619 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10025621221 : Rat) / 4096000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 4096000000), D3 := ((10067686579589843807 : Rat) / 50000000000000000000), D4 := ((8362081280866347949 : Rat) / 25000000000000000000), LB := ((4545834517835079 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((50142915303 : Rat) / 20480000000), D0 := ((50142915303 : Rat) / 20480000000), D1 := ((2584205051 : Rat) / 4096000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10049608945312500057 : Rat) / 50000000000000000000), D4 := ((4176521231863838037 : Rat) / 12500000000000000000), LB := ((22436710711393193 : Rat) / 50000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50142915303 : Rat) / 20480000000), R := ((25075159951 : Rat) / 10240000000), D0 := ((25075159951 : Rat) / 10240000000), D1 := ((6464214927 : Rat) / 10240000000), D2 := ((2243593497 : Rat) / 20480000000), D3 := ((10031531311035156307 : Rat) / 50000000000000000000), D4 := ((8344003646589004199 : Rat) / 25000000000000000000), LB := ((4443407994356441 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25075159951 : Rat) / 10240000000), R := ((50157724501 : Rat) / 20480000000), D0 := ((50157724501 : Rat) / 20480000000), D1 := ((12935834453 : Rat) / 20480000000), D2 := ((1118094449 : Rat) / 10240000000), D3 := ((10013453676757812557 : Rat) / 50000000000000000000), D4 := ((2083741207362583081 : Rat) / 6250000000000000000), LB := ((44140820679591797 : Rat) / 100000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50157724501 : Rat) / 20480000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((2228784299 : Rat) / 20480000000), D3 := ((9995376042480468807 : Rat) / 50000000000000000000), D4 := ((8325926012311660449 : Rat) / 25000000000000000000), LB := ((5499268468100657 : Rat) / 12500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((501651291 : Rat) / 204800000), R := ((50172533699 : Rat) / 20480000000), D0 := ((50172533699 : Rat) / 20480000000), D1 := ((12950643651 : Rat) / 20480000000), D2 := ((22213797 : Rat) / 204800000), D3 := ((9977298408203125057 : Rat) / 50000000000000000000), D4 := ((4158443597586494287 : Rat) / 12500000000000000000), LB := ((2199728473767093 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50172533699 : Rat) / 20480000000), R := ((25089969149 : Rat) / 10240000000), D0 := ((25089969149 : Rat) / 10240000000), D1 := ((51832193 : Rat) / 81920000), D2 := ((2213975101 : Rat) / 20480000000), D3 := ((9959220773925781307 : Rat) / 50000000000000000000), D4 := ((8307848378034316699 : Rat) / 25000000000000000000), LB := ((44142598477650563 : Rat) / 100000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25089969149 : Rat) / 10240000000), R := ((50187342897 : Rat) / 20480000000), D0 := ((50187342897 : Rat) / 20480000000), D1 := ((12965452849 : Rat) / 20480000000), D2 := ((1103285251 : Rat) / 10240000000), D3 := ((9941143139648437557 : Rat) / 50000000000000000000), D4 := ((1037351195111955603 : Rat) / 3125000000000000000), LB := ((2221937583819361 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50187342897 : Rat) / 20480000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((2199165903 : Rat) / 20480000000), D3 := ((9923065505371093807 : Rat) / 50000000000000000000), D4 := ((8289770743756972949 : Rat) / 25000000000000000000), LB := ((112208875911117 : Rat) / 250000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((10040430419 : Rat) / 4096000000), D0 := ((10040430419 : Rat) / 4096000000), D1 := ((12980262047 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((9904987871093750057 : Rat) / 50000000000000000000), D4 := ((4140365963309150537 : Rat) / 12500000000000000000), LB := ((22738760126171653 : Rat) / 50000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10040430419 : Rat) / 4096000000), R := ((25104778347 : Rat) / 10240000000), D0 := ((25104778347 : Rat) / 10240000000), D1 := ((6493833323 : Rat) / 10240000000), D2 := ((436871341 : Rat) / 4096000000), D3 := ((9886910236816406307 : Rat) / 50000000000000000000), D4 := ((8271693109479629199 : Rat) / 25000000000000000000), LB := ((924423830389709 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25104778347 : Rat) / 10240000000), R := ((50216961293 : Rat) / 20480000000), D0 := ((50216961293 : Rat) / 20480000000), D1 := ((2599014249 : Rat) / 4096000000), D2 := ((1088476053 : Rat) / 10240000000), D3 := ((9868832602539062557 : Rat) / 50000000000000000000), D4 := ((2065663573085239331 : Rat) / 6250000000000000000), LB := ((9423019773093233 : Rat) / 20000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50216961293 : Rat) / 20480000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((2169547507 : Rat) / 20480000000), D3 := ((9850754968261718807 : Rat) / 50000000000000000000), D4 := ((8253615475202285449 : Rat) / 25000000000000000000), LB := ((6019972695350817 : Rat) / 12500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((50231770491 : Rat) / 20480000000), D0 := ((50231770491 : Rat) / 20480000000), D1 := ((13009880443 : Rat) / 20480000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((9832677333984375057 : Rat) / 50000000000000000000), D4 := ((4122288329031806787 : Rat) / 12500000000000000000), LB := ((616947293874473 : Rat) / 1250000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50231770491 : Rat) / 20480000000), R := ((5023917509 : Rat) / 2048000000), D0 := ((5023917509 : Rat) / 2048000000), D1 := ((6508642521 : Rat) / 10240000000), D2 := ((2154738309 : Rat) / 20480000000), D3 := ((9814599699707031307 : Rat) / 50000000000000000000), D4 := ((8235537840924941699 : Rat) / 25000000000000000000), LB := ((5070365328558313 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5023917509 : Rat) / 2048000000), R := ((50246579689 : Rat) / 20480000000), D0 := ((50246579689 : Rat) / 20480000000), D1 := ((13024689641 : Rat) / 20480000000), D2 := ((214733371 : Rat) / 2048000000), D3 := ((9796522065429687557 : Rat) / 50000000000000000000), D4 := ((64269523623330233 : Rat) / 195312500000000000), LB := ((5220394420340779 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50246579689 : Rat) / 20480000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((2139929111 : Rat) / 20480000000), D3 := ((9778444431152343807 : Rat) / 50000000000000000000), D4 := ((8217460206647597949 : Rat) / 25000000000000000000), LB := ((1077144287360221 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((50261388887 : Rat) / 20480000000), D0 := ((50261388887 : Rat) / 20480000000), D1 := ((13039498839 : Rat) / 20480000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9760366796875000057 : Rat) / 50000000000000000000), D4 := ((4104210694754463037 : Rat) / 12500000000000000000), LB := ((55664026731711 : Rat) / 100000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50261388887 : Rat) / 20480000000), R := ((25134396743 : Rat) / 10240000000), D0 := ((25134396743 : Rat) / 10240000000), D1 := ((6523451719 : Rat) / 10240000000), D2 := ((2125119913 : Rat) / 20480000000), D3 := ((9742289162597656307 : Rat) / 50000000000000000000), D4 := ((8199382572370254199 : Rat) / 25000000000000000000), LB := ((5762494915198257 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25134396743 : Rat) / 10240000000), R := ((10055239617 : Rat) / 4096000000), D0 := ((10055239617 : Rat) / 4096000000), D1 := ((13054308037 : Rat) / 20480000000), D2 := ((1058857657 : Rat) / 10240000000), D3 := ((9724211528320312557 : Rat) / 50000000000000000000), D4 := ((2047585938807895581 : Rat) / 6250000000000000000), LB := ((5974055445027437 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10055239617 : Rat) / 4096000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((422062143 : Rat) / 4096000000), D3 := ((9706133894042968807 : Rat) / 50000000000000000000), D4 := ((8181304938092910449 : Rat) / 25000000000000000000), LB := ((3100571023564591 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((25149205941 : Rat) / 10240000000), D0 := ((25149205941 : Rat) / 10240000000), D1 := ((6538260917 : Rat) / 10240000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((9688056259765625057 : Rat) / 50000000000000000000), D4 := ((4086133060477119287 : Rat) / 12500000000000000000), LB := ((536342809741297 : Rat) / 12500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25149205941 : Rat) / 10240000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((1044048459 : Rat) / 10240000000), D3 := ((9651900991210937557 : Rat) / 50000000000000000000), D4 := ((1019273560834611853 : Rat) / 3125000000000000000), LB := ((9669784245058821 : Rat) / 100000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((25164015139 : Rat) / 10240000000), D0 := ((25164015139 : Rat) / 10240000000), D1 := ((1310614023 : Rat) / 2048000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9615745722656250057 : Rat) / 50000000000000000000), D4 := ((4068055426199775537 : Rat) / 12500000000000000000), LB := ((7839603422357677 : Rat) / 50000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25164015139 : Rat) / 10240000000), R := ((12585709869 : Rat) / 5120000000), D0 := ((12585709869 : Rat) / 5120000000), D1 := ((3280237357 : Rat) / 5120000000), D2 := ((1029239261 : Rat) / 10240000000), D3 := ((9579590454101562557 : Rat) / 50000000000000000000), D4 := ((2029508304530551831 : Rat) / 6250000000000000000), LB := ((22323863520348763 : Rat) / 100000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12585709869 : Rat) / 5120000000), R := ((25178824337 : Rat) / 10240000000), D0 := ((25178824337 : Rat) / 10240000000), D1 := ((6567879313 : Rat) / 10240000000), D2 := ((510917331 : Rat) / 5120000000), D3 := ((9543435185546875057 : Rat) / 50000000000000000000), D4 := ((4049977791922431787 : Rat) / 12500000000000000000), LB := ((740217375315641 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25178824337 : Rat) / 10240000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((1014430063 : Rat) / 10240000000), D3 := ((9507279916992187557 : Rat) / 50000000000000000000), D4 := ((505117371847969989 : Rat) / 1562500000000000000), LB := ((469234146856963 : Rat) / 1250000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((5038726707 : Rat) / 2048000000), D0 := ((5038726707 : Rat) / 2048000000), D1 := ((6582688511 : Rat) / 10240000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9471124648437500057 : Rat) / 50000000000000000000), D4 := ((4031900157645088037 : Rat) / 12500000000000000000), LB := ((922381922086879 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5038726707 : Rat) / 2048000000), R := ((12600519067 : Rat) / 5120000000), D0 := ((12600519067 : Rat) / 5120000000), D1 := ((659009311 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 2048000000), D3 := ((9434969379882812557 : Rat) / 50000000000000000000), D4 := ((2011430670253208081 : Rat) / 6250000000000000000), LB := ((34596877966293 : Rat) / 62500000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12600519067 : Rat) / 5120000000), R := ((25208442733 : Rat) / 10240000000), D0 := ((25208442733 : Rat) / 10240000000), D1 := ((6597497709 : Rat) / 10240000000), D2 := ((496108133 : Rat) / 5120000000), D3 := ((9398814111328125057 : Rat) / 50000000000000000000), D4 := ((4013822523367744287 : Rat) / 12500000000000000000), LB := ((1631294276288539 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25208442733 : Rat) / 10240000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((984811667 : Rat) / 10240000000), D3 := ((9362658842773437557 : Rat) / 50000000000000000000), D4 := ((1001195926557268103 : Rat) / 3125000000000000000), LB := ((7581480761559567 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((25223251931 : Rat) / 10240000000), D0 := ((25223251931 : Rat) / 10240000000), D1 := ((6612306907 : Rat) / 10240000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9326503574218750057 : Rat) / 50000000000000000000), D4 := ((3995744889090400537 : Rat) / 12500000000000000000), LB := ((4352481442209677 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25223251931 : Rat) / 10240000000), R := ((2523065653 : Rat) / 1024000000), D0 := ((2523065653 : Rat) / 1024000000), D1 := ((3309855753 : Rat) / 5120000000), D2 := ((970002469 : Rat) / 10240000000), D3 := ((9290348305664062557 : Rat) / 50000000000000000000), D4 := ((1993353035975864331 : Rat) / 6250000000000000000), LB := ((4948092681993227 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2523065653 : Rat) / 1024000000), R := ((25238061129 : Rat) / 10240000000), D0 := ((25238061129 : Rat) / 10240000000), D1 := ((1325423221 : Rat) / 2048000000), D2 := ((96259787 : Rat) / 1024000000), D3 := ((9254193037109375057 : Rat) / 50000000000000000000), D4 := ((3977667254813056787 : Rat) / 12500000000000000000), LB := ((1115572081832883 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25238061129 : Rat) / 10240000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((955193271 : Rat) / 10240000000), D3 := ((9218037768554687557 : Rat) / 50000000000000000000), D4 := ((248039277354649057 : Rat) / 781250000000000000), LB := ((1248415288145649 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((197230201 : Rat) / 80000000), R := ((12630137463 : Rat) / 5120000000), D0 := ((12630137463 : Rat) / 5120000000), D1 := ((3324664951 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9181882500000000057 : Rat) / 50000000000000000000), D4 := ((3959589620535713037 : Rat) / 12500000000000000000), LB := ((2518298609536021 : Rat) / 12500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12630137463 : Rat) / 5120000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((466489737 : Rat) / 5120000000), D3 := ((9109571962890625057 : Rat) / 50000000000000000000), D4 := ((3941511986258369287 : Rat) / 12500000000000000000), LB := ((1260746296437923 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((12644946661 : Rat) / 5120000000), D0 := ((12644946661 : Rat) / 5120000000), D1 := ((3339474149 : Rat) / 5120000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9037261425781250057 : Rat) / 50000000000000000000), D4 := ((3923434351981025537 : Rat) / 12500000000000000000), LB := ((1671328743344691 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12644946661 : Rat) / 5120000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 5120000000), D3 := ((8964950888671875057 : Rat) / 50000000000000000000), D4 := ((3905356717703681787 : Rat) / 12500000000000000000), LB := ((2392163017695459 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((632617563 : Rat) / 256000000), R := ((12659755859 : Rat) / 5120000000), D0 := ((12659755859 : Rat) / 5120000000), D1 := ((3354283347 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((8892640351562500057 : Rat) / 50000000000000000000), D4 := ((3887279083426338037 : Rat) / 12500000000000000000), LB := ((15860913693901413 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12659755859 : Rat) / 5120000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((436871341 : Rat) / 5120000000), D3 := ((8820329814453125057 : Rat) / 50000000000000000000), D4 := ((3869201449148994287 : Rat) / 12500000000000000000), LB := ((2507822542523637 : Rat) / 1250000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((8748019277343750057 : Rat) / 50000000000000000000), D4 := ((3851123814871650537 : Rat) / 12500000000000000000), LB := ((449905792558547 : Rat) / 4000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8603398203125000057 : Rat) / 50000000000000000000), D4 := ((3814968546316963037 : Rat) / 12500000000000000000), LB := ((223478769741009 : Rat) / 200000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((8458777128906250057 : Rat) / 50000000000000000000), D4 := ((3778813277762275537 : Rat) / 12500000000000000000), LB := ((4505895332805987 : Rat) / 2000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8314156054687500057 : Rat) / 50000000000000000000), D4 := ((3742658009207588037 : Rat) / 12500000000000000000), LB := ((176243773095211 : Rat) / 50000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8169534980468750057 : Rat) / 50000000000000000000), D4 := ((3706502740652900537 : Rat) / 12500000000000000000), LB := ((2469738193717347 : Rat) / 500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8024913906250000057 : Rat) / 50000000000000000000), D4 := ((3670347472098213037 : Rat) / 12500000000000000000), LB := ((596502969392931 : Rat) / 312500000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((7735671757812500057 : Rat) / 50000000000000000000), D4 := ((3598036934988838037 : Rat) / 12500000000000000000), LB := ((2774778126306221 : Rat) / 500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7446429609375000057 : Rat) / 50000000000000000000), D4 := ((3525726397879463037 : Rat) / 12500000000000000000), LB := ((8756365839357461 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6867945312500000057 : Rat) / 50000000000000000000), D4 := ((3381105323660713037 : Rat) / 12500000000000000000), LB := ((12186722641308573 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6289461015625000057 : Rat) / 50000000000000000000), D4 := ((3236484249441963037 : Rat) / 12500000000000000000), LB := ((27868412718512037 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5710976718750000057 : Rat) / 50000000000000000000), D4 := ((3091863175223213037 : Rat) / 12500000000000000000), LB := ((414885951983297 : Rat) / 12500000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((511587 : Rat) / 200000), R := ((516141008125000000057 : Rat) / 200000000000000000000), D0 := ((516141008125000000057 : Rat) / 200000000000000000000), D1 := ((152645988125000000057 : Rat) / 200000000000000000000), D2 := ((4554008125000000057 : Rat) / 200000000000000000000), D3 := ((4554008125000000057 : Rat) / 50000000000000000000), D4 := ((2802621026785713037 : Rat) / 12500000000000000000), LB := ((5399134899776051 : Rat) / 100000000000000000) }
]

def block393RightChunk000L : Rat := ((43511287946428571513 : Rat) / 25000000000000000000)
def block393RightChunk000R : Rat := ((516141008125000000057 : Rat) / 200000000000000000000)

def block393RightChunk000Certificate : Bool :=
  allBoxesValid block393RightChunk000 &&
  coversFromBool block393RightChunk000 block393RightChunk000L block393RightChunk000R

theorem block393RightChunk000Certificate_eq_true :
    block393RightChunk000Certificate = true := by
  native_decide

def block393RightChunk001 : List RatBox := [
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((516141008125000000057 : Rat) / 200000000000000000000), R := ((260347508125000000057 : Rat) / 100000000000000000000), D0 := ((260347508125000000057 : Rat) / 100000000000000000000), D1 := ((78599998125000000057 : Rat) / 100000000000000000000), D2 := ((4554008125000000057 : Rat) / 100000000000000000000), D3 := ((13662024375000000171 : Rat) / 200000000000000000000), D4 := ((8057585660714281707 : Rat) / 40000000000000000000), LB := ((29200374179026767 : Rat) / 500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((260347508125000000057 : Rat) / 100000000000000000000), R := ((132450758125000000057 : Rat) / 50000000000000000000), D0 := ((132450758125000000057 : Rat) / 50000000000000000000), D1 := ((41577003125000000057 : Rat) / 50000000000000000000), D2 := ((4554008125000000057 : Rat) / 50000000000000000000), D3 := ((4554008125000000057 : Rat) / 100000000000000000000), D4 := ((17866960089285704239 : Rat) / 100000000000000000000), LB := ((2740376642835901 : Rat) / 50000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((132450758125000000057 : Rat) / 50000000000000000000), R := ((134741554285714285827 : Rat) / 50000000000000000000), D0 := ((134741554285714285827 : Rat) / 50000000000000000000), D1 := ((43867799285714285827 : Rat) / 50000000000000000000), D2 := ((6844804285714285827 : Rat) / 50000000000000000000), D3 := ((229079616071428577 : Rat) / 5000000000000000000), D4 := ((6656475982142852091 : Rat) / 50000000000000000000), LB := ((1241775169941773 : Rat) / 62500000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((134741554285714285827 : Rat) / 50000000000000000000), R := ((270628506651785714539 : Rat) / 100000000000000000000), D0 := ((270628506651785714539 : Rat) / 100000000000000000000), D1 := ((88880996651785714539 : Rat) / 100000000000000000000), D2 := ((14835006651785714539 : Rat) / 100000000000000000000), D3 := ((229079616071428577 : Rat) / 4000000000000000000), D4 := ((4365679821428566321 : Rat) / 50000000000000000000), LB := ((25093207933454653 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((270628506651785714539 : Rat) / 100000000000000000000), R := ((542402411383928571963 : Rat) / 200000000000000000000), D0 := ((542402411383928571963 : Rat) / 200000000000000000000), D1 := ((178907391383928571963 : Rat) / 200000000000000000000), D2 := ((30815411383928571963 : Rat) / 200000000000000000000), D3 := ((2519875776785714347 : Rat) / 40000000000000000000), D4 := ((7585961562499989757 : Rat) / 100000000000000000000), LB := ((20397563897953663 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((542402411383928571963 : Rat) / 200000000000000000000), R := ((16985869045758928589 : Rat) / 6250000000000000000), D0 := ((16985869045758928589 : Rat) / 6250000000000000000), D1 := ((5626649670758928589 : Rat) / 6250000000000000000), D2 := ((998775295758928589 : Rat) / 6250000000000000000), D3 := ((687238848214285731 : Rat) / 10000000000000000000), D4 := ((14026525044642836629 : Rat) / 200000000000000000000), LB := ((4078734080582319 : Rat) / 500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((16985869045758928589 : Rat) / 6250000000000000000), R := ((1088241017008928572581 : Rat) / 400000000000000000000), D0 := ((1088241017008928572581 : Rat) / 400000000000000000000), D1 := ((361250977008928572581 : Rat) / 400000000000000000000), D2 := ((65067017008928572581 : Rat) / 400000000000000000000), D3 := ((229079616071428577 : Rat) / 3200000000000000000), D4 := ((805070435267855859 : Rat) / 12500000000000000000), LB := ((230935583114783 : Rat) / 25000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1088241017008928572581 : Rat) / 400000000000000000000), R := ((544693207544642857733 : Rat) / 200000000000000000000), D0 := ((544693207544642857733 : Rat) / 200000000000000000000), D1 := ((181198187544642857733 : Rat) / 200000000000000000000), D2 := ((33106207544642857733 : Rat) / 200000000000000000000), D3 := ((2978035008928571501 : Rat) / 40000000000000000000), D4 := ((24616855848214244603 : Rat) / 400000000000000000000), LB := ((4819819689452887 : Rat) / 1000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((544693207544642857733 : Rat) / 200000000000000000000), R := ((1090531813169642858351 : Rat) / 400000000000000000000), D0 := ((1090531813169642858351 : Rat) / 400000000000000000000), D1 := ((363541773169642858351 : Rat) / 400000000000000000000), D2 := ((67357813169642858351 : Rat) / 400000000000000000000), D3 := ((6185149633928571579 : Rat) / 80000000000000000000), D4 := ((11735728883928550859 : Rat) / 200000000000000000000), LB := ((2486631659860683 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1090531813169642858351 : Rat) / 400000000000000000000), R := ((2182209024419642859587 : Rat) / 800000000000000000000), D0 := ((2182209024419642859587 : Rat) / 800000000000000000000), D1 := ((728228944419642859587 : Rat) / 800000000000000000000), D2 := ((135861024419642859587 : Rat) / 800000000000000000000), D3 := ((2519875776785714347 : Rat) / 32000000000000000000), D4 := ((22326059687499958833 : Rat) / 400000000000000000000), LB := ((751079262993129 : Rat) / 250000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2182209024419642859587 : Rat) / 800000000000000000000), R := ((272919302812500000309 : Rat) / 100000000000000000000), D0 := ((272919302812500000309 : Rat) / 100000000000000000000), D1 := ((91171792812500000309 : Rat) / 100000000000000000000), D2 := ((17125802812500000309 : Rat) / 100000000000000000000), D3 := ((1603557312500000039 : Rat) / 20000000000000000000), D4 := ((43506721294642774781 : Rat) / 800000000000000000000), LB := ((783517668470457 : Rat) / 500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((272919302812500000309 : Rat) / 100000000000000000000), R := ((2184499820580357145357 : Rat) / 800000000000000000000), D0 := ((2184499820580357145357 : Rat) / 800000000000000000000), D1 := ((730519740580357145357 : Rat) / 800000000000000000000), D2 := ((138151820580357145357 : Rat) / 800000000000000000000), D3 := ((13057538116071428889 : Rat) / 160000000000000000000), D4 := ((5295165401785703987 : Rat) / 100000000000000000000), LB := ((2909421356987463 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2184499820580357145357 : Rat) / 800000000000000000000), R := ((4370145039241071433599 : Rat) / 1600000000000000000000), D0 := ((4370145039241071433599 : Rat) / 1600000000000000000000), D1 := ((1462184879241071433599 : Rat) / 1600000000000000000000), D2 := ((277449039241071433599 : Rat) / 1600000000000000000000), D3 := ((5268831169642857271 : Rat) / 64000000000000000000), D4 := ((41215925133928489011 : Rat) / 800000000000000000000), LB := ((17283340749328913 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4370145039241071433599 : Rat) / 1600000000000000000000), R := ((1092822609330357144121 : Rat) / 400000000000000000000), D0 := ((1092822609330357144121 : Rat) / 400000000000000000000), D1 := ((365832569330357144121 : Rat) / 400000000000000000000), D2 := ((69648609330357144121 : Rat) / 400000000000000000000), D3 := ((6643308866071428733 : Rat) / 80000000000000000000), D4 := ((81286452187499835137 : Rat) / 1600000000000000000000), LB := ((3054241412621811 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1092822609330357144121 : Rat) / 400000000000000000000), R := ((4372435835401785719369 : Rat) / 1600000000000000000000), D0 := ((4372435835401785719369 : Rat) / 1600000000000000000000), D1 := ((1464475675401785719369 : Rat) / 1600000000000000000000), D2 := ((279739835401785719369 : Rat) / 1600000000000000000000), D3 := ((26802315080357143509 : Rat) / 320000000000000000000), D4 := ((20035263526785673063 : Rat) / 400000000000000000000), LB := ((3790404800736169 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4372435835401785719369 : Rat) / 1600000000000000000000), R := ((2186790616741071431127 : Rat) / 800000000000000000000), D0 := ((2186790616741071431127 : Rat) / 800000000000000000000), D1 := ((732810536741071431127 : Rat) / 800000000000000000000), D2 := ((140442616741071431127 : Rat) / 800000000000000000000), D3 := ((13515697348214286043 : Rat) / 160000000000000000000), D4 := ((78995656026785549367 : Rat) / 1600000000000000000000), LB := ((2113109183632389 : Rat) / 6250000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2186790616741071431127 : Rat) / 800000000000000000000), R := ((8748307865044642867393 : Rat) / 3200000000000000000000), D0 := ((8748307865044642867393 : Rat) / 3200000000000000000000), D1 := ((2932387545044642867393 : Rat) / 3200000000000000000000), D2 := ((562915865044642867393 : Rat) / 3200000000000000000000), D3 := ((54291869008928572749 : Rat) / 640000000000000000000), D4 := ((38925128973214203241 : Rat) / 800000000000000000000), LB := ((3035845155013317 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8748307865044642867393 : Rat) / 3200000000000000000000), R := ((4374726631562500005139 : Rat) / 1600000000000000000000), D0 := ((4374726631562500005139 : Rat) / 1600000000000000000000), D1 := ((1466766471562500005139 : Rat) / 1600000000000000000000), D2 := ((282030631562500005139 : Rat) / 1600000000000000000000), D3 := ((27260474312500000663 : Rat) / 320000000000000000000), D4 := ((154555117812499670079 : Rat) / 3200000000000000000000), LB := ((2599911570665553 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4374726631562500005139 : Rat) / 1600000000000000000000), R := ((8750598661205357153163 : Rat) / 3200000000000000000000), D0 := ((8750598661205357153163 : Rat) / 3200000000000000000000), D1 := ((2934678341205357153163 : Rat) / 3200000000000000000000), D2 := ((565206661205357153163 : Rat) / 3200000000000000000000), D3 := ((54750028241071429903 : Rat) / 640000000000000000000), D4 := ((76704859866071263597 : Rat) / 1600000000000000000000), LB := ((8769532096596921 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8750598661205357153163 : Rat) / 3200000000000000000000), R := ((546984003705357143503 : Rat) / 200000000000000000000), D0 := ((546984003705357143503 : Rat) / 200000000000000000000), D1 := ((183488983705357143503 : Rat) / 200000000000000000000), D2 := ((35397003705357143503 : Rat) / 200000000000000000000), D3 := ((687238848214285731 : Rat) / 8000000000000000000), D4 := ((152264321651785384309 : Rat) / 3200000000000000000000), LB := ((7253977934640887 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((546984003705357143503 : Rat) / 200000000000000000000), R := ((8752889457366071438933 : Rat) / 3200000000000000000000), D0 := ((8752889457366071438933 : Rat) / 3200000000000000000000), D1 := ((2936969137366071438933 : Rat) / 3200000000000000000000), D2 := ((567497457366071438933 : Rat) / 3200000000000000000000), D3 := ((55208187473214287057 : Rat) / 640000000000000000000), D4 := ((9444932723214265089 : Rat) / 200000000000000000000), LB := ((5853954092865377 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8752889457366071438933 : Rat) / 3200000000000000000000), R := ((4377017427723214290909 : Rat) / 1600000000000000000000), D0 := ((4377017427723214290909 : Rat) / 1600000000000000000000), D1 := ((1469057267723214290909 : Rat) / 1600000000000000000000), D2 := ((284321427723214290909 : Rat) / 1600000000000000000000), D3 := ((27718633544642857817 : Rat) / 320000000000000000000), D4 := ((149973525491071098539 : Rat) / 3200000000000000000000), LB := ((11426155165485119 : Rat) / 25000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4377017427723214290909 : Rat) / 1600000000000000000000), R := ((8755180253526785724703 : Rat) / 3200000000000000000000), D0 := ((8755180253526785724703 : Rat) / 3200000000000000000000), D1 := ((2939259933526785724703 : Rat) / 3200000000000000000000), D2 := ((569788253526785724703 : Rat) / 3200000000000000000000), D3 := ((55666346705357144211 : Rat) / 640000000000000000000), D4 := ((74414063705356977827 : Rat) / 1600000000000000000000), LB := ((851133839195467 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8755180253526785724703 : Rat) / 3200000000000000000000), R := ((2189081412901785716897 : Rat) / 800000000000000000000), D0 := ((2189081412901785716897 : Rat) / 800000000000000000000), D1 := ((735101332901785716897 : Rat) / 800000000000000000000), D2 := ((142733412901785716897 : Rat) / 800000000000000000000), D3 := ((13973856580357143197 : Rat) / 160000000000000000000), D4 := ((147682729330356812769 : Rat) / 3200000000000000000000), LB := ((5893100791447281 : Rat) / 25000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2189081412901785716897 : Rat) / 800000000000000000000), R := ((8757471049687500010473 : Rat) / 3200000000000000000000), D0 := ((8757471049687500010473 : Rat) / 3200000000000000000000), D1 := ((2941550729687500010473 : Rat) / 3200000000000000000000), D2 := ((572079049687500010473 : Rat) / 3200000000000000000000), D3 := ((11224901187500000273 : Rat) / 128000000000000000000), D4 := ((36634332812499917471 : Rat) / 800000000000000000000), LB := ((357419256464403 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8757471049687500010473 : Rat) / 3200000000000000000000), R := ((4379308223883928576679 : Rat) / 1600000000000000000000), D0 := ((4379308223883928576679 : Rat) / 1600000000000000000000), D1 := ((1471348063883928576679 : Rat) / 1600000000000000000000), D2 := ((286612223883928576679 : Rat) / 1600000000000000000000), D3 := ((28176792776785714971 : Rat) / 320000000000000000000), D4 := ((145391933169642526999 : Rat) / 3200000000000000000000), LB := ((778725261303681 : Rat) / 12500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4379308223883928576679 : Rat) / 1600000000000000000000), R := ((17518378293616071449601 : Rat) / 6400000000000000000000), D0 := ((17518378293616071449601 : Rat) / 6400000000000000000000), D1 := ((5886537653616071449601 : Rat) / 6400000000000000000000), D2 := ((1147594293616071449601 : Rat) / 6400000000000000000000), D3 := ((112936250723214288461 : Rat) / 1280000000000000000000), D4 := ((72123267544642692057 : Rat) / 1600000000000000000000), LB := ((3024043144661537 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17518378293616071449601 : Rat) / 6400000000000000000000), R := ((8759761845848214296243 : Rat) / 3200000000000000000000), D0 := ((8759761845848214296243 : Rat) / 3200000000000000000000), D1 := ((2943841525848214296243 : Rat) / 3200000000000000000000), D2 := ((574369845848214296243 : Rat) / 3200000000000000000000), D3 := ((56582665169642858519 : Rat) / 640000000000000000000), D4 := ((287347672098213625343 : Rat) / 6400000000000000000000), LB := ((2872045182000793 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8759761845848214296243 : Rat) / 3200000000000000000000), R := ((17520669089776785735371 : Rat) / 6400000000000000000000), D0 := ((17520669089776785735371 : Rat) / 6400000000000000000000), D1 := ((5888828449776785735371 : Rat) / 6400000000000000000000), D2 := ((1149885089776785735371 : Rat) / 6400000000000000000000), D3 := ((22678881991071429123 : Rat) / 256000000000000000000), D4 := ((143101137008928241229 : Rat) / 3200000000000000000000), LB := ((2735544273427537 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17520669089776785735371 : Rat) / 6400000000000000000000), R := ((1095113405491071429891 : Rat) / 400000000000000000000), D0 := ((1095113405491071429891 : Rat) / 400000000000000000000), D1 := ((368123365491071429891 : Rat) / 400000000000000000000), D2 := ((71939405491071429891 : Rat) / 400000000000000000000), D3 := ((7101468098214285887 : Rat) / 80000000000000000000), D4 := ((285056875937499339573 : Rat) / 6400000000000000000000), LB := ((2614618708294547 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1095113405491071429891 : Rat) / 400000000000000000000), R := ((17522959885937500021141 : Rat) / 6400000000000000000000), D0 := ((17522959885937500021141 : Rat) / 6400000000000000000000), D1 := ((5891119245937500021141 : Rat) / 6400000000000000000000), D2 := ((1152175885937500021141 : Rat) / 6400000000000000000000), D3 := ((113852569187500002769 : Rat) / 1280000000000000000000), D4 := ((17744467366071387293 : Rat) / 400000000000000000000), LB := ((2509347986411059 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17522959885937500021141 : Rat) / 6400000000000000000000), R := ((8762052642008928582013 : Rat) / 3200000000000000000000), D0 := ((8762052642008928582013 : Rat) / 3200000000000000000000), D1 := ((2946132322008928582013 : Rat) / 3200000000000000000000), D2 := ((576660642008928582013 : Rat) / 3200000000000000000000), D3 := ((57040824401785715673 : Rat) / 640000000000000000000), D4 := ((282766079776785053803 : Rat) / 6400000000000000000000), LB := ((48396256709398733 : Rat) / 100000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8762052642008928582013 : Rat) / 3200000000000000000000), R := ((17525250682098214306911 : Rat) / 6400000000000000000000), D0 := ((17525250682098214306911 : Rat) / 6400000000000000000000), D1 := ((5893410042098214306911 : Rat) / 6400000000000000000000), D2 := ((1154466682098214306911 : Rat) / 6400000000000000000000), D3 := ((114310728419642859923 : Rat) / 1280000000000000000000), D4 := ((140810340848213955459 : Rat) / 3200000000000000000000), LB := ((1173047614457523 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17525250682098214306911 : Rat) / 6400000000000000000000), R := ((4381599020044642862449 : Rat) / 1600000000000000000000), D0 := ((4381599020044642862449 : Rat) / 1600000000000000000000), D1 := ((1473638860044642862449 : Rat) / 1600000000000000000000), D2 := ((288903020044642862449 : Rat) / 1600000000000000000000), D3 := ((229079616071428577 : Rat) / 2560000000000000000), D4 := ((280475283616070768033 : Rat) / 6400000000000000000000), LB := ((22882784041425297 : Rat) / 50000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4381599020044642862449 : Rat) / 1600000000000000000000), R := ((17527541478258928592681 : Rat) / 6400000000000000000000), D0 := ((17527541478258928592681 : Rat) / 6400000000000000000000), D1 := ((5895700838258928592681 : Rat) / 6400000000000000000000), D2 := ((1156757478258928592681 : Rat) / 6400000000000000000000), D3 := ((114768887651785717077 : Rat) / 1280000000000000000000), D4 := ((69832471383928406287 : Rat) / 1600000000000000000000), LB := ((4492893762260697 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17527541478258928592681 : Rat) / 6400000000000000000000), R := ((8764343438169642867783 : Rat) / 3200000000000000000000), D0 := ((8764343438169642867783 : Rat) / 3200000000000000000000), D1 := ((2948423118169642867783 : Rat) / 3200000000000000000000), D2 := ((578951438169642867783 : Rat) / 3200000000000000000000), D3 := ((57498983633928572827 : Rat) / 640000000000000000000), D4 := ((278184487455356482263 : Rat) / 6400000000000000000000), LB := ((11103432407401359 : Rat) / 25000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8764343438169642867783 : Rat) / 3200000000000000000000), R := ((17529832274419642878451 : Rat) / 6400000000000000000000), D0 := ((17529832274419642878451 : Rat) / 6400000000000000000000), D1 := ((5897991634419642878451 : Rat) / 6400000000000000000000), D2 := ((1159048274419642878451 : Rat) / 6400000000000000000000), D3 := ((115227046883928574231 : Rat) / 1280000000000000000000), D4 := ((138519544687499669689 : Rat) / 3200000000000000000000), LB := ((4422168695636941 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17529832274419642878451 : Rat) / 6400000000000000000000), R := ((2191372209062500002667 : Rat) / 800000000000000000000), D0 := ((2191372209062500002667 : Rat) / 800000000000000000000), D1 := ((737392129062500002667 : Rat) / 800000000000000000000), D2 := ((145024209062500002667 : Rat) / 800000000000000000000), D3 := ((14432015812500000351 : Rat) / 160000000000000000000), D4 := ((275893691294642196493 : Rat) / 6400000000000000000000), LB := ((4435457927373099 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2191372209062500002667 : Rat) / 800000000000000000000), R := ((17532123070580357164221 : Rat) / 6400000000000000000000), D0 := ((17532123070580357164221 : Rat) / 6400000000000000000000), D1 := ((5900282430580357164221 : Rat) / 6400000000000000000000), D2 := ((1161339070580357164221 : Rat) / 6400000000000000000000), D3 := ((23137041223214286277 : Rat) / 256000000000000000000), D4 := ((34343536651785631701 : Rat) / 800000000000000000000), LB := ((22407101738014523 : Rat) / 50000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17532123070580357164221 : Rat) / 6400000000000000000000), R := ((8766634234330357153553 : Rat) / 3200000000000000000000), D0 := ((8766634234330357153553 : Rat) / 3200000000000000000000), D1 := ((2950713914330357153553 : Rat) / 3200000000000000000000), D2 := ((581242234330357153553 : Rat) / 3200000000000000000000), D3 := ((57957142866071429981 : Rat) / 640000000000000000000), D4 := ((273602895133927910723 : Rat) / 6400000000000000000000), LB := ((45602384096449233 : Rat) / 100000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8766634234330357153553 : Rat) / 3200000000000000000000), R := ((17534413866741071449991 : Rat) / 6400000000000000000000), D0 := ((17534413866741071449991 : Rat) / 6400000000000000000000), D1 := ((5902573226741071449991 : Rat) / 6400000000000000000000), D2 := ((1163629866741071449991 : Rat) / 6400000000000000000000), D3 := ((116143365348214288539 : Rat) / 1280000000000000000000), D4 := ((136228748526785383919 : Rat) / 3200000000000000000000), LB := ((2336048686519543 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17534413866741071449991 : Rat) / 6400000000000000000000), R := ((4383889816205357148219 : Rat) / 1600000000000000000000), D0 := ((4383889816205357148219 : Rat) / 1600000000000000000000), D1 := ((1475929656205357148219 : Rat) / 1600000000000000000000), D2 := ((291193816205357148219 : Rat) / 1600000000000000000000), D3 := ((29093111241071429279 : Rat) / 320000000000000000000), D4 := ((271312098973213624953 : Rat) / 6400000000000000000000), LB := ((4817185346893127 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4383889816205357148219 : Rat) / 1600000000000000000000), R := ((17536704662901785735761 : Rat) / 6400000000000000000000), D0 := ((17536704662901785735761 : Rat) / 6400000000000000000000), D1 := ((5904864022901785735761 : Rat) / 6400000000000000000000), D2 := ((1165920662901785735761 : Rat) / 6400000000000000000000), D3 := ((116601524580357145693 : Rat) / 1280000000000000000000), D4 := ((67541675223214120517 : Rat) / 1600000000000000000000), LB := ((2497846667049719 : Rat) / 5000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17536704662901785735761 : Rat) / 6400000000000000000000), R := ((8768925030491071439323 : Rat) / 3200000000000000000000), D0 := ((8768925030491071439323 : Rat) / 3200000000000000000000), D1 := ((2953004710491071439323 : Rat) / 3200000000000000000000), D2 := ((583533030491071439323 : Rat) / 3200000000000000000000), D3 := ((11683060419642857427 : Rat) / 128000000000000000000), D4 := ((269021302812499339183 : Rat) / 6400000000000000000000), LB := ((5207815276630501 : Rat) / 10000000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8768925030491071439323 : Rat) / 3200000000000000000000), R := ((17538995459062500021531 : Rat) / 6400000000000000000000), D0 := ((17538995459062500021531 : Rat) / 6400000000000000000000), D1 := ((5907154819062500021531 : Rat) / 6400000000000000000000), D2 := ((1168211459062500021531 : Rat) / 6400000000000000000000), D3 := ((117059683812500002847 : Rat) / 1280000000000000000000), D4 := ((133937952366071098149 : Rat) / 3200000000000000000000), LB := ((1363437025442421 : Rat) / 2500000000000000000) },
  { w1 := ((50123610034503 : Rat) / 62500000000000), w2 := ((4092803739623337 : Rat) / 100000000000000000), w3 := ((17210002328261223 : Rat) / 100000000000000000), w4 := ((2918805832577957 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132450758125000000057 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17538995459062500021531 : Rat) / 6400000000000000000000), R := ((137032350446428571597 : Rat) / 50000000000000000000), D0 := ((137032350446428571597 : Rat) / 50000000000000000000), D1 := ((46158595446428571597 : Rat) / 50000000000000000000), D2 := ((9135600446428571597 : Rat) / 50000000000000000000), D3 := ((229079616071428577 : Rat) / 2500000000000000000), D4 := ((266730506651785053413 : Rat) / 6400000000000000000000), LB := ((716711471174733 : Rat) / 1250000000000000000) }
]

def block393RightChunk001L : Rat := ((516141008125000000057 : Rat) / 200000000000000000000)
def block393RightChunk001R : Rat := ((137032350446428571597 : Rat) / 50000000000000000000)

def block393RightChunk001Certificate : Bool :=
  allBoxesValid block393RightChunk001 &&
  coversFromBool block393RightChunk001 block393RightChunk001L block393RightChunk001R

theorem block393RightChunk001Certificate_eq_true :
    block393RightChunk001Certificate = true := by
  native_decide

def block393RightChainCertificate : Bool :=
  decide (
    block393RightL = ((43511287946428571513 : Rat) / 25000000000000000000) /\
    ((516141008125000000057 : Rat) / 200000000000000000000) = ((516141008125000000057 : Rat) / 200000000000000000000) /\
    ((137032350446428571597 : Rat) / 50000000000000000000) = block393RightR)

theorem block393RightChainCertificate_eq_true :
    block393RightChainCertificate = true := by
  native_decide

def block393LeftBoxCount : Nat := boxCount block393LeftBoxes
def block393RightBoxCount : Nat := 146

def block393_rational_certificate : Prop :=
    block393LeftCertificate = true /\
    block393RightChainCertificate = true /\
    block393RightChunk000Certificate = true /\
    block393RightChunk001Certificate = true

theorem block393_rational_certificate_proof :
    block393_rational_certificate := by
  exact ⟨block393LeftCertificate_eq_true, block393RightChainCertificate_eq_true, block393RightChunk000Certificate_eq_true, block393RightChunk001Certificate_eq_true⟩

end Block393
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block393

open Set

def block393W1 : Rat := ((50123610034503 : Rat) / 62500000000000)
def block393W2 : Rat := ((4092803739623337 : Rat) / 100000000000000000)
def block393W3 : Rat := ((17210002328261223 : Rat) / 100000000000000000)
def block393W4 : Rat := ((2918805832577957 : Rat) / 20000000000000000)
def block393S1 : Rat := ((18174751 : Rat) / 10000000)
def block393S2 : Rat := ((511587 : Rat) / 200000)
def block393S3 : Rat := ((132450758125000000057 : Rat) / 50000000000000000000)
def block393S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block393V (y : ℝ) : ℝ :=
  ratPotential block393W1 block393W2 block393W3 block393W4 block393S1 block393S2 block393S3 block393S4 y

def block393LeftParamsCertificate : Bool :=
  allBoxesSameParams block393LeftBoxes block393W1 block393W2 block393W3 block393W4 block393S1 block393S2 block393S3 block393S4

theorem block393LeftParamsCertificate_eq_true :
    block393LeftParamsCertificate = true := by
  native_decide

theorem block393_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block393LeftL : ℝ) (block393LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block393S1 : ℝ))
    (hy2ne : y ≠ (block393S2 : ℝ))
    (hy3ne : y ≠ (block393S3 : ℝ))
    (hy4ne : y ≠ (block393S4 : ℝ)) :
    0 < block393V y := by
  have hcert := block393LeftCertificate_eq_true
  unfold block393LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block393LeftBoxes) (lo := block393LeftL) (hi := block393LeftR)
    (w1 := block393W1) (w2 := block393W2) (w3 := block393W3) (w4 := block393W4)
    (s1 := block393S1) (s2 := block393S2) (s3 := block393S3) (s4 := block393S4)
    hboxes hcover block393LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block393RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block393RightChunk000 block393W1 block393W2 block393W3 block393W4 block393S1 block393S2 block393S3 block393S4

theorem block393RightChunk000ParamsCertificate_eq_true :
    block393RightChunk000ParamsCertificate = true := by
  native_decide

theorem block393_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block393RightChunk000L : ℝ) (block393RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block393S1 : ℝ))
    (hy2ne : y ≠ (block393S2 : ℝ))
    (hy3ne : y ≠ (block393S3 : ℝ))
    (hy4ne : y ≠ (block393S4 : ℝ)) :
    0 < block393V y := by
  have hcert := block393RightChunk000Certificate_eq_true
  unfold block393RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block393RightChunk000) (lo := block393RightChunk000L) (hi := block393RightChunk000R)
    (w1 := block393W1) (w2 := block393W2) (w3 := block393W3) (w4 := block393W4)
    (s1 := block393S1) (s2 := block393S2) (s3 := block393S3) (s4 := block393S4)
    hboxes hcover block393RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block393RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block393RightChunk001 block393W1 block393W2 block393W3 block393W4 block393S1 block393S2 block393S3 block393S4

theorem block393RightChunk001ParamsCertificate_eq_true :
    block393RightChunk001ParamsCertificate = true := by
  native_decide

theorem block393_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block393RightChunk001L : ℝ) (block393RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block393S1 : ℝ))
    (hy2ne : y ≠ (block393S2 : ℝ))
    (hy3ne : y ≠ (block393S3 : ℝ))
    (hy4ne : y ≠ (block393S4 : ℝ)) :
    0 < block393V y := by
  have hcert := block393RightChunk001Certificate_eq_true
  unfold block393RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block393RightChunk001) (lo := block393RightChunk001L) (hi := block393RightChunk001R)
    (w1 := block393W1) (w2 := block393W2) (w3 := block393W3) (w4 := block393W4)
    (s1 := block393S1) (s2 := block393S2) (s3 := block393S3) (s4 := block393S4)
    hboxes hcover block393RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block393_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block393RightL : ℝ) (block393RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block393S1 : ℝ))
    (hy2ne : y ≠ (block393S2 : ℝ))
    (hy3ne : y ≠ (block393S3 : ℝ))
    (hy4ne : y ≠ (block393S4 : ℝ)) :
    0 < block393V y := by
  by_cases h0 : y ≤ (block393RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block393RightChunk000L : ℝ) (block393RightChunk000R : ℝ) := by
      have hL : (block393RightChunk000L : ℝ) = (block393RightL : ℝ) := by
        norm_num [block393RightChunk000L, block393RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block393_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block393RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block393RightChunk001L : ℝ) = (block393RightChunk000R : ℝ) := by
      norm_num [block393RightChunk001L, block393RightChunk000R]
    have hR : (block393RightChunk001R : ℝ) = (block393RightR : ℝ) := by
      norm_num [block393RightChunk001R, block393RightR]
    have hyc : y ∈ Icc (block393RightChunk001L : ℝ) (block393RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block393_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block393_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block393LeftL : ℝ) (block393LeftR : ℝ) →
    y ≠ 0 → y ≠ (block393S1 : ℝ) → y ≠ (block393S2 : ℝ) →
    y ≠ (block393S3 : ℝ) → y ≠ (block393S4 : ℝ) → 0 < block393V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block393RightL : ℝ) (block393RightR : ℝ) →
    y ≠ 0 → y ≠ (block393S1 : ℝ) → y ≠ (block393S2 : ℝ) →
    y ≠ (block393S3 : ℝ) → y ≠ (block393S4 : ℝ) → 0 < block393V y)

theorem block393_reallog_certificate_proof :
    block393_reallog_certificate := by
  exact ⟨block393_left_V_pos, block393_right_V_pos⟩

end Block393
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block393.block393V
#check Erdos1038Lean.M1817475.Block393.block393_left_V_pos
#check Erdos1038Lean.M1817475.Block393.block393_right_V_pos
#check Erdos1038Lean.M1817475.Block393.block393_reallog_certificate_proof
