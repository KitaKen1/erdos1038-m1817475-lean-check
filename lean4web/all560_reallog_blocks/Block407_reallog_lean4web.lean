/-
Self-contained Lean4Web paste file.
Block 407 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block407

def block407LeftL : Rat := ((4610716517857142879 : Rat) / 6250000000000000000)
def block407LeftR : Rat := ((36895506696428571603 : Rat) / 50000000000000000000)
def block407RightL : Rat := ((10860716517857142879 : Rat) / 6250000000000000000)
def block407RightR : Rat := ((136895506696428571603 : Rat) / 50000000000000000000)

def block407LeftBoxes : List RatBox := [
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4610716517857142879 : Rat) / 6250000000000000000), R := ((36895506696428571603 : Rat) / 50000000000000000000), D0 := ((36895506696428571603 : Rat) / 50000000000000000000), D1 := ((6748502857142857121 : Rat) / 6250000000000000000), D2 := ((11376377232142857121 : Rat) / 6250000000000000000), D3 := ((95291338482142857037 : Rat) / 50000000000000000000), D4 := ((799521848493303531 : Rat) / 390625000000000000), LB := ((1521100632600747 : Rat) / 5000000000000000000) }
]

def block407LeftCertificate : Bool :=
  allBoxesValid block407LeftBoxes &&
  coversFromBool block407LeftBoxes block407LeftL block407LeftR

theorem block407LeftCertificate_eq_true :
    block407LeftCertificate = true := by
  native_decide

def block407RightChunk000 : List RatBox := [
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((10860716517857142879 : Rat) / 6250000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((498502857142857121 : Rat) / 6250000000000000000), D2 := ((5126377232142857121 : Rat) / 6250000000000000000), D3 := ((45291338482142857037 : Rat) / 50000000000000000000), D4 := ((408896848493303531 : Rat) / 390625000000000000), LB := ((1267851230316173 : Rat) / 1000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41303315625000000069 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((295521052878377 : Rat) / 500000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((32047566875000000069 : Rat) / 50000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((8903058186899297 : Rat) / 100000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((22791818125000000069 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((12325656916561123 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18163943750000000069 : Rat) / 50000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((8024521308468087 : Rat) / 200000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((17006975156250000069 : Rat) / 50000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((3831305926584161 : Rat) / 200000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((15850006562500000069 : Rat) / 50000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((131942490380893 : Rat) / 100000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((14693037968750000069 : Rat) / 50000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((1730373076527729 : Rat) / 250000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((14114553671875000069 : Rat) / 50000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((2635907094943879 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13536069375000000069 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((153586003138331 : Rat) / 31250000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((13246827226562500069 : Rat) / 50000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((6047856995450747 : Rat) / 2500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((12957585078125000069 : Rat) / 50000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((634922463881471 : Rat) / 4000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((12668342929687500069 : Rat) / 50000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((1498374178199223 : Rat) / 500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((12523721855468750069 : Rat) / 50000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((20588444418405683 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1228212131 : Rat) / 512000000), D0 := ((1228212131 : Rat) / 512000000), D1 := ((1488324399 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12379100781250000069 : Rat) / 50000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((2366649907439039 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1228212131 : Rat) / 512000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 512000000), D3 := ((12234479707031250069 : Rat) / 50000000000000000000), D4 := ((3856387566406249 : Rat) / 10000000000000000), LB := ((741934500388397 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((12304335107 : Rat) / 5120000000), D0 := ((12304335107 : Rat) / 5120000000), D1 := ((599772519 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((12089858632812500069 : Rat) / 50000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((20200399832201593 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12304335107 : Rat) / 5120000000), R := ((6155869853 : Rat) / 2560000000), D0 := ((6155869853 : Rat) / 2560000000), D1 := ((1503133597 : Rat) / 2560000000), D2 := ((792292093 : Rat) / 5120000000), D3 := ((12017548095703125069 : Rat) / 50000000000000000000), D4 := ((238312577758789 : Rat) / 625000000000000), LB := ((8326621274455867 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6155869853 : Rat) / 2560000000), R := ((2463828861 : Rat) / 1024000000), D0 := ((2463828861 : Rat) / 1024000000), D1 := ((3013671793 : Rat) / 5120000000), D2 := ((392443747 : Rat) / 2560000000), D3 := ((11945237558593750069 : Rat) / 50000000000000000000), D4 := ((3798539136718749 : Rat) / 10000000000000000), LB := ((2653893103253091 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2463828861 : Rat) / 1024000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((155496579 : Rat) / 1024000000), D3 := ((11872927021484375069 : Rat) / 50000000000000000000), D4 := ((1892038514648437 : Rat) / 5000000000000000), LB := ((2512548026303539 : Rat) / 2500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((12333953503 : Rat) / 5120000000), D0 := ((12333953503 : Rat) / 5120000000), D1 := ((3028480991 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((11800616484375000069 : Rat) / 50000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((3498285622757849 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12333953503 : Rat) / 5120000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((762673697 : Rat) / 5120000000), D3 := ((11728305947265625069 : Rat) / 50000000000000000000), D4 := ((938788203613281 : Rat) / 2500000000000000), LB := ((8219555977192483 : Rat) / 20000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((12348762701 : Rat) / 5120000000), D0 := ((12348762701 : Rat) / 5120000000), D1 := ((3043290189 : Rat) / 5120000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((11655995410156250069 : Rat) / 50000000000000000000), D4 := ((3740690707031249 : Rat) / 10000000000000000), LB := ((6955070441912181 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12348762701 : Rat) / 5120000000), R := ((24704930001 : Rat) / 10240000000), D0 := ((24704930001 : Rat) / 10240000000), D1 := ((6093984977 : Rat) / 10240000000), D2 := ((747864499 : Rat) / 5120000000), D3 := ((11583684873046875069 : Rat) / 50000000000000000000), D4 := ((1863114299804687 : Rat) / 5000000000000000), LB := ((5340608296095159 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24704930001 : Rat) / 10240000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((1488324399 : Rat) / 10240000000), D3 := ((11547529604492187569 : Rat) / 50000000000000000000), D4 := ((7437995091796873 : Rat) / 20000000000000000), LB := ((1891740887621507 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((24719739199 : Rat) / 10240000000), D0 := ((24719739199 : Rat) / 10240000000), D1 := ((244351767 : Rat) / 409600000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11511374335937500069 : Rat) / 50000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((206975174790687 : Rat) / 250000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24719739199 : Rat) / 10240000000), R := ((12363571899 : Rat) / 5120000000), D0 := ((12363571899 : Rat) / 5120000000), D1 := ((3058099387 : Rat) / 5120000000), D2 := ((1473515201 : Rat) / 10240000000), D3 := ((11475219067382812569 : Rat) / 50000000000000000000), D4 := ((7409070876953123 : Rat) / 20000000000000000), LB := ((714228574723641 : Rat) / 1000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12363571899 : Rat) / 5120000000), R := ((24734548397 : Rat) / 10240000000), D0 := ((24734548397 : Rat) / 10240000000), D1 := ((6123603373 : Rat) / 10240000000), D2 := ((733055301 : Rat) / 5120000000), D3 := ((11439063798828125069 : Rat) / 50000000000000000000), D4 := ((462163048095703 : Rat) / 1250000000000000), LB := ((6048704025841539 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24734548397 : Rat) / 10240000000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((1458706003 : Rat) / 10240000000), D3 := ((11402908530273437569 : Rat) / 50000000000000000000), D4 := ((7380146662109373 : Rat) / 20000000000000000), LB := ((999685399167699 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((4949871519 : Rat) / 2048000000), D0 := ((4949871519 : Rat) / 2048000000), D1 := ((6138412571 : Rat) / 10240000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((11366753261718750069 : Rat) / 50000000000000000000), D4 := ((3682842277343749 : Rat) / 10000000000000000), LB := ((997905423639027 : Rat) / 2500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4949871519 : Rat) / 2048000000), R := ((12378381097 : Rat) / 5120000000), D0 := ((12378381097 : Rat) / 5120000000), D1 := ((614581717 : Rat) / 1024000000), D2 := ((288779361 : Rat) / 2048000000), D3 := ((11330597993164062569 : Rat) / 50000000000000000000), D4 := ((7351222447265623 : Rat) / 20000000000000000), LB := ((3028457050015393 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12378381097 : Rat) / 5120000000), R := ((24764166793 : Rat) / 10240000000), D0 := ((24764166793 : Rat) / 10240000000), D1 := ((6153221769 : Rat) / 10240000000), D2 := ((718246103 : Rat) / 5120000000), D3 := ((11294442724609375069 : Rat) / 50000000000000000000), D4 := ((1834190084960937 : Rat) / 5000000000000000), LB := ((10545519515496593 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24764166793 : Rat) / 10240000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((1429087607 : Rat) / 10240000000), D3 := ((11258287456054687569 : Rat) / 50000000000000000000), D4 := ((7322298232421873 : Rat) / 20000000000000000), LB := ((12337350300140049 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((24778975991 : Rat) / 10240000000), D0 := ((24778975991 : Rat) / 10240000000), D1 := ((6168030967 : Rat) / 10240000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11222132187500000069 : Rat) / 50000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((8050503303064227 : Rat) / 200000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24778975991 : Rat) / 10240000000), R := ((49565356581 : Rat) / 20480000000), D0 := ((49565356581 : Rat) / 20480000000), D1 := ((12343466533 : Rat) / 20480000000), D2 := ((1414278409 : Rat) / 10240000000), D3 := ((11185976918945312569 : Rat) / 50000000000000000000), D4 := ((7293374017578123 : Rat) / 20000000000000000), LB := ((5476559224923683 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49565356581 : Rat) / 20480000000), R := ((2478638059 : Rat) / 1024000000), D0 := ((2478638059 : Rat) / 1024000000), D1 := ((3087717783 : Rat) / 5120000000), D2 := ((2821152219 : Rat) / 20480000000), D3 := ((11167899284667968819 : Rat) / 50000000000000000000), D4 := ((14572285927734371 : Rat) / 40000000000000000), LB := ((5096963324235371 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2478638059 : Rat) / 1024000000), R := ((49580165779 : Rat) / 20480000000), D0 := ((49580165779 : Rat) / 20480000000), D1 := ((12358275731 : Rat) / 20480000000), D2 := ((140687381 : Rat) / 1024000000), D3 := ((11149821650390625069 : Rat) / 50000000000000000000), D4 := ((909863988769531 : Rat) / 2500000000000000), LB := ((147766304219683 : Rat) / 312500000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49580165779 : Rat) / 20480000000), R := ((24793785189 : Rat) / 10240000000), D0 := ((24793785189 : Rat) / 10240000000), D1 := ((1236568033 : Rat) / 2048000000), D2 := ((2806343021 : Rat) / 20480000000), D3 := ((11131744016113281319 : Rat) / 50000000000000000000), D4 := ((14543361712890621 : Rat) / 40000000000000000), LB := ((4371257108969073 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24793785189 : Rat) / 10240000000), R := ((49594974977 : Rat) / 20480000000), D0 := ((49594974977 : Rat) / 20480000000), D1 := ((12373084929 : Rat) / 20480000000), D2 := ((1399469211 : Rat) / 10240000000), D3 := ((11113666381835937569 : Rat) / 50000000000000000000), D4 := ((7264449802734373 : Rat) / 20000000000000000), LB := ((805038445218037 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49594974977 : Rat) / 20480000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((2791533823 : Rat) / 20480000000), D3 := ((11095588747558593819 : Rat) / 50000000000000000000), D4 := ((14514437498046871 : Rat) / 40000000000000000), LB := ((3690349995537773 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((1984391367 : Rat) / 819200000), D0 := ((1984391367 : Rat) / 819200000), D1 := ((12387894127 : Rat) / 20480000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((11077511113281250069 : Rat) / 50000000000000000000), D4 := ((3624993847656249 : Rat) / 10000000000000000), LB := ((1683376728187913 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1984391367 : Rat) / 819200000), R := ((24808594387 : Rat) / 10240000000), D0 := ((24808594387 : Rat) / 10240000000), D1 := ((6197649363 : Rat) / 10240000000), D2 := ((22213797 : Rat) / 163840000), D3 := ((11059433479003906319 : Rat) / 50000000000000000000), D4 := ((14485513283203121 : Rat) / 40000000000000000), LB := ((152721288917107 : Rat) / 500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24808594387 : Rat) / 10240000000), R := ((49624593373 : Rat) / 20480000000), D0 := ((49624593373 : Rat) / 20480000000), D1 := ((496108133 : Rat) / 819200000), D2 := ((1384660013 : Rat) / 10240000000), D3 := ((11041355844726562569 : Rat) / 50000000000000000000), D4 := ((7235525587890623 : Rat) / 20000000000000000), LB := ((6883475656635149 : Rat) / 25000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49624593373 : Rat) / 20480000000), R := ((12407999493 : Rat) / 5120000000), D0 := ((12407999493 : Rat) / 5120000000), D1 := ((3102526981 : Rat) / 5120000000), D2 := ((2761915427 : Rat) / 20480000000), D3 := ((11023278210449218819 : Rat) / 50000000000000000000), D4 := ((14456589068359371 : Rat) / 40000000000000000), LB := ((24636703428077 : Rat) / 100000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12407999493 : Rat) / 5120000000), R := ((49639402571 : Rat) / 20480000000), D0 := ((49639402571 : Rat) / 20480000000), D1 := ((12417512523 : Rat) / 20480000000), D2 := ((688627707 : Rat) / 5120000000), D3 := ((11005200576171875069 : Rat) / 50000000000000000000), D4 := ((1805265870117187 : Rat) / 5000000000000000), LB := ((10926447926915689 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49639402571 : Rat) / 20480000000), R := ((4964680717 : Rat) / 2048000000), D0 := ((4964680717 : Rat) / 2048000000), D1 := ((6212458561 : Rat) / 10240000000), D2 := ((2747106229 : Rat) / 20480000000), D3 := ((10987122941894531319 : Rat) / 50000000000000000000), D4 := ((14427664853515621 : Rat) / 40000000000000000), LB := ((2397839613563213 : Rat) / 12500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4964680717 : Rat) / 2048000000), R := ((49654211769 : Rat) / 20480000000), D0 := ((49654211769 : Rat) / 20480000000), D1 := ((12432321721 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 2048000000), D3 := ((10969045307617187569 : Rat) / 50000000000000000000), D4 := ((7206601373046873 : Rat) / 20000000000000000), LB := ((16626404943832773 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49654211769 : Rat) / 20480000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((2732297031 : Rat) / 20480000000), D3 := ((10950967673339843819 : Rat) / 50000000000000000000), D4 := ((14398740638671871 : Rat) / 40000000000000000), LB := ((7092099833478499 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((49669020967 : Rat) / 20480000000), D0 := ((49669020967 : Rat) / 20480000000), D1 := ((12447130919 : Rat) / 20480000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((10932890039062500069 : Rat) / 50000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((474253685944781 : Rat) / 4000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49669020967 : Rat) / 20480000000), R := ((24838212783 : Rat) / 10240000000), D0 := ((24838212783 : Rat) / 10240000000), D1 := ((6227267759 : Rat) / 10240000000), D2 := ((2717487833 : Rat) / 20480000000), D3 := ((10914812404785156319 : Rat) / 50000000000000000000), D4 := ((14369816423828121 : Rat) / 40000000000000000), LB := ((4821537415843763 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24838212783 : Rat) / 10240000000), R := ((9936766033 : Rat) / 4096000000), D0 := ((9936766033 : Rat) / 4096000000), D1 := ((12461940117 : Rat) / 20480000000), D2 := ((1355041617 : Rat) / 10240000000), D3 := ((10896734770507812569 : Rat) / 50000000000000000000), D4 := ((7177677158203123 : Rat) / 20000000000000000), LB := ((3772320769757087 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9936766033 : Rat) / 4096000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((540535727 : Rat) / 4096000000), D3 := ((10878657136230468819 : Rat) / 50000000000000000000), D4 := ((14340892208984371 : Rat) / 40000000000000000), LB := ((2780643742203437 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((49698639363 : Rat) / 20480000000), D0 := ((49698639363 : Rat) / 20480000000), D1 := ((2495349863 : Rat) / 4096000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((10860579501953125069 : Rat) / 50000000000000000000), D4 := ((111925235168457 : Rat) / 312500000000000), LB := ((923314819117893 : Rat) / 25000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49698639363 : Rat) / 20480000000), R := ((24853021981 : Rat) / 10240000000), D0 := ((24853021981 : Rat) / 10240000000), D1 := ((6242076957 : Rat) / 10240000000), D2 := ((2687869437 : Rat) / 20480000000), D3 := ((10842501867675781319 : Rat) / 50000000000000000000), D4 := ((14311967994140621 : Rat) / 40000000000000000), LB := ((485201232973409 : Rat) / 25000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24853021981 : Rat) / 10240000000), R := ((49713448561 : Rat) / 20480000000), D0 := ((49713448561 : Rat) / 20480000000), D1 := ((12491558513 : Rat) / 20480000000), D2 := ((1340232419 : Rat) / 10240000000), D3 := ((10824424233398437569 : Rat) / 50000000000000000000), D4 := ((7148752943359373 : Rat) / 20000000000000000), LB := ((3041738821138451 : Rat) / 1000000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49713448561 : Rat) / 20480000000), R := ((99434301721 : Rat) / 40960000000), D0 := ((99434301721 : Rat) / 40960000000), D1 := ((199924173 : Rat) / 327680000), D2 := ((2673060239 : Rat) / 20480000000), D3 := ((10806346599121093819 : Rat) / 50000000000000000000), D4 := ((14283043779296871 : Rat) / 40000000000000000), LB := ((347545555842519 : Rat) / 1250000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99434301721 : Rat) / 40960000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((5338715879 : Rat) / 40960000000), D3 := ((1349663472747802743 : Rat) / 6250000000000000000), D4 := ((28551625451171867 : Rat) / 80000000000000000), LB := ((27080028820800073 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((99449110919 : Rat) / 40960000000), D0 := ((99449110919 : Rat) / 40960000000), D1 := ((25005330823 : Rat) / 40960000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((10788268964843750069 : Rat) / 50000000000000000000), D4 := ((3567145417968749 : Rat) / 10000000000000000), LB := ((412273910907761 : Rat) / 1562500000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99449110919 : Rat) / 40960000000), R := ((49728257759 : Rat) / 20480000000), D0 := ((49728257759 : Rat) / 20480000000), D1 := ((12506367711 : Rat) / 20480000000), D2 := ((5323906681 : Rat) / 40960000000), D3 := ((5389615073852539097 : Rat) / 25000000000000000000), D4 := ((28522701236328117 : Rat) / 80000000000000000), LB := ((2572018065733761 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49728257759 : Rat) / 20480000000), R := ((99463920117 : Rat) / 40960000000), D0 := ((99463920117 : Rat) / 40960000000), D1 := ((25020140021 : Rat) / 40960000000), D2 := ((2658251041 : Rat) / 20480000000), D3 := ((10770191330566406319 : Rat) / 50000000000000000000), D4 := ((14254119564453121 : Rat) / 40000000000000000), LB := ((1254200587354551 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99463920117 : Rat) / 40960000000), R := ((24867831179 : Rat) / 10240000000), D0 := ((24867831179 : Rat) / 10240000000), D1 := ((1251377231 : Rat) / 2048000000), D2 := ((5309097483 : Rat) / 40960000000), D3 := ((2690288128356933611 : Rat) / 12500000000000000000), D4 := ((28493777021484367 : Rat) / 80000000000000000), LB := ((2447705550693291 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24867831179 : Rat) / 10240000000), R := ((19895745863 : Rat) / 8192000000), D0 := ((19895745863 : Rat) / 8192000000), D1 := ((25034949219 : Rat) / 40960000000), D2 := ((1325423221 : Rat) / 10240000000), D3 := ((10752113696289062569 : Rat) / 50000000000000000000), D4 := ((7119828728515623 : Rat) / 20000000000000000), LB := ((11949671983869231 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((19895745863 : Rat) / 8192000000), R := ((49743066957 : Rat) / 20480000000), D0 := ((49743066957 : Rat) / 20480000000), D1 := ((12521176909 : Rat) / 20480000000), D2 := ((1058857657 : Rat) / 8192000000), D3 := ((5371537439575195347 : Rat) / 25000000000000000000), D4 := ((28464852806640617 : Rat) / 80000000000000000), LB := ((2335090925188743 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49743066957 : Rat) / 20480000000), R := ((99493538513 : Rat) / 40960000000), D0 := ((99493538513 : Rat) / 40960000000), D1 := ((25049758417 : Rat) / 40960000000), D2 := ((2643441843 : Rat) / 20480000000), D3 := ((10734036062011718819 : Rat) / 50000000000000000000), D4 := ((14225195349609371 : Rat) / 40000000000000000), LB := ((713493236675607 : Rat) / 3125000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99493538513 : Rat) / 40960000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((5279479087 : Rat) / 40960000000), D3 := ((335156163902282717 : Rat) / 1562500000000000000), D4 := ((28435928591796867 : Rat) / 80000000000000000), LB := ((1396374952447859 : Rat) / 6250000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((99508347711 : Rat) / 40960000000), D0 := ((99508347711 : Rat) / 40960000000), D1 := ((5012913523 : Rat) / 8192000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((10715958427734375069 : Rat) / 50000000000000000000), D4 := ((1776341655273437 : Rat) / 5000000000000000), LB := ((10940794323629349 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99508347711 : Rat) / 40960000000), R := ((9951575231 : Rat) / 4096000000), D0 := ((9951575231 : Rat) / 4096000000), D1 := ((12535986107 : Rat) / 20480000000), D2 := ((5264669889 : Rat) / 40960000000), D3 := ((5353459805297851597 : Rat) / 25000000000000000000), D4 := ((28407004376953117 : Rat) / 80000000000000000), LB := ((10725292144640741 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9951575231 : Rat) / 4096000000), R := ((99523156909 : Rat) / 40960000000), D0 := ((99523156909 : Rat) / 40960000000), D1 := ((25079376813 : Rat) / 40960000000), D2 := ((525726529 : Rat) / 4096000000), D3 := ((10697880793457031319 : Rat) / 50000000000000000000), D4 := ((14196271134765621 : Rat) / 40000000000000000), LB := ((263112734370987 : Rat) / 1250000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99523156909 : Rat) / 40960000000), R := ((24882640377 : Rat) / 10240000000), D0 := ((24882640377 : Rat) / 10240000000), D1 := ((6271695353 : Rat) / 10240000000), D2 := ((5249860691 : Rat) / 40960000000), D3 := ((2672210494079589861 : Rat) / 12500000000000000000), D4 := ((28378080162109367 : Rat) / 80000000000000000), LB := ((20676924706128363 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24882640377 : Rat) / 10240000000), R := ((99537966107 : Rat) / 40960000000), D0 := ((99537966107 : Rat) / 40960000000), D1 := ((25094186011 : Rat) / 40960000000), D2 := ((1310614023 : Rat) / 10240000000), D3 := ((10679803159179687569 : Rat) / 50000000000000000000), D4 := ((7090904513671873 : Rat) / 20000000000000000), LB := ((508358373243617 : Rat) / 2500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99537966107 : Rat) / 40960000000), R := ((49772685353 : Rat) / 20480000000), D0 := ((49772685353 : Rat) / 20480000000), D1 := ((2510159061 : Rat) / 4096000000), D2 := ((5235051493 : Rat) / 40960000000), D3 := ((5335382171020507847 : Rat) / 25000000000000000000), D4 := ((28349155947265617 : Rat) / 80000000000000000), LB := ((10010641142880333 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49772685353 : Rat) / 20480000000), R := ((19910555061 : Rat) / 8192000000), D0 := ((19910555061 : Rat) / 8192000000), D1 := ((25108995209 : Rat) / 40960000000), D2 := ((2613823447 : Rat) / 20480000000), D3 := ((10661725524902343819 : Rat) / 50000000000000000000), D4 := ((14167346919921871 : Rat) / 40000000000000000), LB := ((157902397867693 : Rat) / 800000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((19910555061 : Rat) / 8192000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((1044048459 : Rat) / 8192000000), D3 := ((1331585838470458993 : Rat) / 6250000000000000000), D4 := ((28320231732421867 : Rat) / 80000000000000000), LB := ((974196016327103 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((99567584503 : Rat) / 40960000000), D0 := ((99567584503 : Rat) / 40960000000), D1 := ((25123804407 : Rat) / 40960000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((10643647890625000069 : Rat) / 50000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((385193544270801 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99567584503 : Rat) / 40960000000), R := ((49787494551 : Rat) / 20480000000), D0 := ((49787494551 : Rat) / 20480000000), D1 := ((12565604503 : Rat) / 20480000000), D2 := ((5205433097 : Rat) / 40960000000), D3 := ((5317304536743164097 : Rat) / 25000000000000000000), D4 := ((28291307517578117 : Rat) / 80000000000000000), LB := ((9532551819058793 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49787494551 : Rat) / 20480000000), R := ((99582393701 : Rat) / 40960000000), D0 := ((99582393701 : Rat) / 40960000000), D1 := ((5027722721 : Rat) / 8192000000), D2 := ((2599014249 : Rat) / 20480000000), D3 := ((10625570256347656319 : Rat) / 50000000000000000000), D4 := ((14138422705078121 : Rat) / 40000000000000000), LB := ((3780046587823771 : Rat) / 20000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99582393701 : Rat) / 40960000000), R := ((995897983 : Rat) / 409600000), D0 := ((995897983 : Rat) / 409600000), D1 := ((6286504551 : Rat) / 10240000000), D2 := ((5190623899 : Rat) / 40960000000), D3 := ((2654132859802246111 : Rat) / 12500000000000000000), D4 := ((28262383302734367 : Rat) / 80000000000000000), LB := ((4691274637831297 : Rat) / 25000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((995897983 : Rat) / 409600000), R := ((99597202899 : Rat) / 40960000000), D0 := ((99597202899 : Rat) / 40960000000), D1 := ((25153422803 : Rat) / 40960000000), D2 := ((51832193 : Rat) / 409600000), D3 := ((10607492622070312569 : Rat) / 50000000000000000000), D4 := ((7061980298828123 : Rat) / 20000000000000000), LB := ((3731946801079633 : Rat) / 20000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99597202899 : Rat) / 40960000000), R := ((49802303749 : Rat) / 20480000000), D0 := ((49802303749 : Rat) / 20480000000), D1 := ((12580413701 : Rat) / 20480000000), D2 := ((5175814701 : Rat) / 40960000000), D3 := ((5299226902465820347 : Rat) / 25000000000000000000), D4 := ((28233459087890617 : Rat) / 80000000000000000), LB := ((18584172928100273 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49802303749 : Rat) / 20480000000), R := ((99612012097 : Rat) / 40960000000), D0 := ((99612012097 : Rat) / 40960000000), D1 := ((25168232001 : Rat) / 40960000000), D2 := ((2584205051 : Rat) / 20480000000), D3 := ((10589414987792968819 : Rat) / 50000000000000000000), D4 := ((14109498490234371 : Rat) / 40000000000000000), LB := ((2317306130388691 : Rat) / 12500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99612012097 : Rat) / 40960000000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((5161005503 : Rat) / 40960000000), D3 := ((661273510665893559 : Rat) / 3125000000000000000), D4 := ((28204534873046867 : Rat) / 80000000000000000), LB := ((9261298085386921 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((19925364259 : Rat) / 8192000000), D0 := ((19925364259 : Rat) / 8192000000), D1 := ((25183041199 : Rat) / 40960000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((10571337353515625069 : Rat) / 50000000000000000000), D4 := ((880939773925781 : Rat) / 2500000000000000), LB := ((1853664822881601 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((19925364259 : Rat) / 8192000000), R := ((49817112947 : Rat) / 20480000000), D0 := ((49817112947 : Rat) / 20480000000), D1 := ((12595222899 : Rat) / 20480000000), D2 := ((1029239261 : Rat) / 8192000000), D3 := ((5281149268188476597 : Rat) / 25000000000000000000), D4 := ((28175610658203117 : Rat) / 80000000000000000), LB := ((92903196162189 : Rat) / 500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49817112947 : Rat) / 20480000000), R := ((99641630493 : Rat) / 40960000000), D0 := ((99641630493 : Rat) / 40960000000), D1 := ((25197850397 : Rat) / 40960000000), D2 := ((2569395853 : Rat) / 20480000000), D3 := ((10553259719238281319 : Rat) / 50000000000000000000), D4 := ((14080574275390621 : Rat) / 40000000000000000), LB := ((18654603294683547 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99641630493 : Rat) / 40960000000), R := ((24912258773 : Rat) / 10240000000), D0 := ((24912258773 : Rat) / 10240000000), D1 := ((6301313749 : Rat) / 10240000000), D2 := ((5131387107 : Rat) / 40960000000), D3 := ((2636055225524902361 : Rat) / 12500000000000000000), D4 := ((28146686443359367 : Rat) / 80000000000000000), LB := ((18758574626744073 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24912258773 : Rat) / 10240000000), R := ((99656439691 : Rat) / 40960000000), D0 := ((99656439691 : Rat) / 40960000000), D1 := ((5042531919 : Rat) / 8192000000), D2 := ((1280995627 : Rat) / 10240000000), D3 := ((10535182084960937569 : Rat) / 50000000000000000000), D4 := ((7033056083984373 : Rat) / 20000000000000000), LB := ((18892587538232863 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99656439691 : Rat) / 40960000000), R := ((9966384429 : Rat) / 4096000000), D0 := ((9966384429 : Rat) / 4096000000), D1 := ((12610032097 : Rat) / 20480000000), D2 := ((5116577909 : Rat) / 40960000000), D3 := ((5263071633911132847 : Rat) / 25000000000000000000), D4 := ((28117762228515617 : Rat) / 80000000000000000), LB := ((9528338218885851 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9966384429 : Rat) / 4096000000), R := ((99671248889 : Rat) / 40960000000), D0 := ((99671248889 : Rat) / 40960000000), D1 := ((25227468793 : Rat) / 40960000000), D2 := ((510917331 : Rat) / 4096000000), D3 := ((10517104450683593819 : Rat) / 50000000000000000000), D4 := ((14051650060546871 : Rat) / 40000000000000000), LB := ((601589869777229 : Rat) / 3125000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99671248889 : Rat) / 40960000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((5101768711 : Rat) / 40960000000), D3 := ((1313508204193115243 : Rat) / 6250000000000000000), D4 := ((28088838013671867 : Rat) / 80000000000000000), LB := ((97376101652967 : Rat) / 500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((99686058087 : Rat) / 40960000000), D0 := ((99686058087 : Rat) / 40960000000), D1 := ((25242277991 : Rat) / 40960000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10499026816406250069 : Rat) / 50000000000000000000), D4 := ((3509296988281249 : Rat) / 10000000000000000), LB := ((19729744637721203 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99686058087 : Rat) / 40960000000), R := ((49846731343 : Rat) / 20480000000), D0 := ((49846731343 : Rat) / 20480000000), D1 := ((2524968259 : Rat) / 4096000000), D2 := ((5086959513 : Rat) / 40960000000), D3 := ((5244993999633789097 : Rat) / 25000000000000000000), D4 := ((28059913798828117 : Rat) / 80000000000000000), LB := ((10007241780588677 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49846731343 : Rat) / 20480000000), R := ((19940173457 : Rat) / 8192000000), D0 := ((19940173457 : Rat) / 8192000000), D1 := ((25257087189 : Rat) / 40960000000), D2 := ((2539777457 : Rat) / 20480000000), D3 := ((10480949182128906319 : Rat) / 50000000000000000000), D4 := ((14022725845703121 : Rat) / 40000000000000000), LB := ((4065894401645287 : Rat) / 20000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((19940173457 : Rat) / 8192000000), R := ((24927067971 : Rat) / 10240000000), D0 := ((24927067971 : Rat) / 10240000000), D1 := ((6316122947 : Rat) / 10240000000), D2 := ((1014430063 : Rat) / 8192000000), D3 := ((2617977591247558611 : Rat) / 12500000000000000000), D4 := ((28030989583984367 : Rat) / 80000000000000000), LB := ((5168686246699583 : Rat) / 25000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24927067971 : Rat) / 10240000000), R := ((99715676483 : Rat) / 40960000000), D0 := ((99715676483 : Rat) / 40960000000), D1 := ((25271896387 : Rat) / 40960000000), D2 := ((1266186429 : Rat) / 10240000000), D3 := ((10462871547851562569 : Rat) / 50000000000000000000), D4 := ((7004131869140623 : Rat) / 20000000000000000), LB := ((21050337606089153 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99715676483 : Rat) / 40960000000), R := ((49861540541 : Rat) / 20480000000), D0 := ((49861540541 : Rat) / 20480000000), D1 := ((12639650493 : Rat) / 20480000000), D2 := ((5057341117 : Rat) / 40960000000), D3 := ((5226916365356445347 : Rat) / 25000000000000000000), D4 := ((28002065369140617 : Rat) / 80000000000000000), LB := ((5364071269129897 : Rat) / 25000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49861540541 : Rat) / 20480000000), R := ((99730485681 : Rat) / 40960000000), D0 := ((99730485681 : Rat) / 40960000000), D1 := ((5057341117 : Rat) / 8192000000), D2 := ((2524968259 : Rat) / 20480000000), D3 := ((10444793913574218819 : Rat) / 50000000000000000000), D4 := ((13993801630859371 : Rat) / 40000000000000000), LB := ((4378524542063833 : Rat) / 20000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99730485681 : Rat) / 40960000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((5042531919 : Rat) / 40960000000), D3 := ((163058673381805421 : Rat) / 781250000000000000), D4 := ((27973141154296867 : Rat) / 80000000000000000), LB := ((11179692960812393 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((99745294879 : Rat) / 40960000000), D0 := ((99745294879 : Rat) / 40960000000), D1 := ((25301514783 : Rat) / 40960000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((10426716279296875069 : Rat) / 50000000000000000000), D4 := ((1747417440429687 : Rat) / 5000000000000000), LB := ((22856610227192653 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99745294879 : Rat) / 40960000000), R := ((49876349739 : Rat) / 20480000000), D0 := ((49876349739 : Rat) / 20480000000), D1 := ((12654459691 : Rat) / 20480000000), D2 := ((5027722721 : Rat) / 40960000000), D3 := ((5208838731079101597 : Rat) / 25000000000000000000), D4 := ((27944216939453117 : Rat) / 80000000000000000), LB := ((4676866249249123 : Rat) / 20000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49876349739 : Rat) / 20480000000), R := ((99760104077 : Rat) / 40960000000), D0 := ((99760104077 : Rat) / 40960000000), D1 := ((25316323981 : Rat) / 40960000000), D2 := ((2510159061 : Rat) / 20480000000), D3 := ((10408638645019531319 : Rat) / 50000000000000000000), D4 := ((13964877416015621 : Rat) / 40000000000000000), LB := ((11971292350619611 : Rat) / 50000000000000000000) }
]

def block407RightChunk000L : Rat := ((10860716517857142879 : Rat) / 6250000000000000000)
def block407RightChunk000R : Rat := ((99760104077 : Rat) / 40960000000)

def block407RightChunk000Certificate : Bool :=
  allBoxesValid block407RightChunk000 &&
  coversFromBool block407RightChunk000 block407RightChunk000L block407RightChunk000R

theorem block407RightChunk000Certificate_eq_true :
    block407RightChunk000Certificate = true := by
  native_decide

def block407RightChunk001 : List RatBox := [
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99760104077 : Rat) / 40960000000), R := ((24941877169 : Rat) / 10240000000), D0 := ((24941877169 : Rat) / 10240000000), D1 := ((1266186429 : Rat) / 2048000000), D2 := ((5012913523 : Rat) / 40960000000), D3 := ((2599899956970214861 : Rat) / 12500000000000000000), D4 := ((27915292724609367 : Rat) / 80000000000000000), LB := ((306642580225093 : Rat) / 1250000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24941877169 : Rat) / 10240000000), R := ((3990996531 : Rat) / 1638400000), D0 := ((3990996531 : Rat) / 1638400000), D1 := ((25331133179 : Rat) / 40960000000), D2 := ((1251377231 : Rat) / 10240000000), D3 := ((10390561010742187569 : Rat) / 50000000000000000000), D4 := ((6975207654296873 : Rat) / 20000000000000000), LB := ((12575416163009 : Rat) / 50000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3990996531 : Rat) / 1638400000), R := ((49891158937 : Rat) / 20480000000), D0 := ((49891158937 : Rat) / 20480000000), D1 := ((12669268889 : Rat) / 20480000000), D2 := ((199924173 : Rat) / 1638400000), D3 := ((5190761096801757847 : Rat) / 25000000000000000000), D4 := ((27886368509765617 : Rat) / 80000000000000000), LB := ((12900449229432537 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49891158937 : Rat) / 20480000000), R := ((99789722473 : Rat) / 40960000000), D0 := ((99789722473 : Rat) / 40960000000), D1 := ((25345942377 : Rat) / 40960000000), D2 := ((2495349863 : Rat) / 20480000000), D3 := ((10372483376464843819 : Rat) / 50000000000000000000), D4 := ((13935953201171871 : Rat) / 40000000000000000), LB := ((3310205119318177 : Rat) / 12500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99789722473 : Rat) / 40960000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((4983295127 : Rat) / 40960000000), D3 := ((1295430569915771493 : Rat) / 6250000000000000000), D4 := ((27857444294921867 : Rat) / 80000000000000000), LB := ((5438619211185769 : Rat) / 20000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((99804531671 : Rat) / 40960000000), D0 := ((99804531671 : Rat) / 40960000000), D1 := ((1014430063 : Rat) / 1638400000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10354405742187500069 : Rat) / 50000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((3491912513853973 : Rat) / 12500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((99804531671 : Rat) / 40960000000), R := ((9981193627 : Rat) / 4096000000), D0 := ((9981193627 : Rat) / 4096000000), D1 := ((12684078087 : Rat) / 20480000000), D2 := ((4968485929 : Rat) / 40960000000), D3 := ((5172683462524414097 : Rat) / 25000000000000000000), D4 := ((27828520080078117 : Rat) / 80000000000000000), LB := ((14354144786304923 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9981193627 : Rat) / 4096000000), R := ((24956686367 : Rat) / 10240000000), D0 := ((24956686367 : Rat) / 10240000000), D1 := ((6345741343 : Rat) / 10240000000), D2 := ((496108133 : Rat) / 4096000000), D3 := ((10336328107910156319 : Rat) / 50000000000000000000), D4 := ((13907028986328121 : Rat) / 40000000000000000), LB := ((8480976599903323 : Rat) / 1000000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24956686367 : Rat) / 10240000000), R := ((49920777333 : Rat) / 20480000000), D0 := ((49920777333 : Rat) / 20480000000), D1 := ((2539777457 : Rat) / 4096000000), D2 := ((1236568033 : Rat) / 10240000000), D3 := ((10318250473632812569 : Rat) / 50000000000000000000), D4 := ((6946283439453123 : Rat) / 20000000000000000), LB := ((2561823777547101 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49920777333 : Rat) / 20480000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((2465731467 : Rat) / 20480000000), D3 := ((10300172839355468819 : Rat) / 50000000000000000000), D4 := ((13878104771484371 : Rat) / 40000000000000000), LB := ((2199632179820249 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((49935586531 : Rat) / 20480000000), D0 := ((49935586531 : Rat) / 20480000000), D1 := ((12713696483 : Rat) / 20480000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((10282095205078125069 : Rat) / 50000000000000000000), D4 := ((433238833251953 : Rat) / 1250000000000000), LB := ((6360715749353929 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49935586531 : Rat) / 20480000000), R := ((4994299113 : Rat) / 2048000000), D0 := ((4994299113 : Rat) / 2048000000), D1 := ((6360550541 : Rat) / 10240000000), D2 := ((2450922269 : Rat) / 20480000000), D3 := ((10264017570800781319 : Rat) / 50000000000000000000), D4 := ((13849180556640621 : Rat) / 40000000000000000), LB := ((4223238008227437 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4994299113 : Rat) / 2048000000), R := ((49950395729 : Rat) / 20480000000), D0 := ((49950395729 : Rat) / 20480000000), D1 := ((12728505681 : Rat) / 20480000000), D2 := ((244351767 : Rat) / 2048000000), D3 := ((10245939936523437569 : Rat) / 50000000000000000000), D4 := ((6917359224609373 : Rat) / 20000000000000000), LB := ((5328422484426193 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49950395729 : Rat) / 20480000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((2436113071 : Rat) / 20480000000), D3 := ((10227862302246093819 : Rat) / 50000000000000000000), D4 := ((13820256341796871 : Rat) / 40000000000000000), LB := ((6496062082163301 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((49965204927 : Rat) / 20480000000), D0 := ((49965204927 : Rat) / 20480000000), D1 := ((12743314879 : Rat) / 20480000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10209784667968750069 : Rat) / 50000000000000000000), D4 := ((3451448558593749 : Rat) / 10000000000000000), LB := ((772630846114647 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49965204927 : Rat) / 20480000000), R := ((24986304763 : Rat) / 10240000000), D0 := ((24986304763 : Rat) / 10240000000), D1 := ((6375359739 : Rat) / 10240000000), D2 := ((2421303873 : Rat) / 20480000000), D3 := ((10191707033691406319 : Rat) / 50000000000000000000), D4 := ((13791332126953121 : Rat) / 40000000000000000), LB := ((9019314167683923 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24986304763 : Rat) / 10240000000), R := ((399840113 : Rat) / 163840000), D0 := ((399840113 : Rat) / 163840000), D1 := ((12758124077 : Rat) / 20480000000), D2 := ((1206949637 : Rat) / 10240000000), D3 := ((10173629399414062569 : Rat) / 50000000000000000000), D4 := ((6888435009765623 : Rat) / 20000000000000000), LB := ((20750465281488273 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((399840113 : Rat) / 163840000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 819200000), D3 := ((10155551765136718819 : Rat) / 50000000000000000000), D4 := ((13762407912109371 : Rat) / 40000000000000000), LB := ((2948554554515169 : Rat) / 12500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((49994823323 : Rat) / 20480000000), D0 := ((49994823323 : Rat) / 20480000000), D1 := ((510917331 : Rat) / 819200000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((10137474130859375069 : Rat) / 50000000000000000000), D4 := ((1718493225585937 : Rat) / 5000000000000000), LB := ((2655285228385651 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49994823323 : Rat) / 20480000000), R := ((25001113961 : Rat) / 10240000000), D0 := ((25001113961 : Rat) / 10240000000), D1 := ((6390168937 : Rat) / 10240000000), D2 := ((2391685477 : Rat) / 20480000000), D3 := ((10119396496582031319 : Rat) / 50000000000000000000), D4 := ((13733483697265621 : Rat) / 40000000000000000), LB := ((29644025131359 : Rat) / 100000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25001113961 : Rat) / 10240000000), R := ((50009632521 : Rat) / 20480000000), D0 := ((50009632521 : Rat) / 20480000000), D1 := ((12787742473 : Rat) / 20480000000), D2 := ((1192140439 : Rat) / 10240000000), D3 := ((10101318862304687569 : Rat) / 50000000000000000000), D4 := ((6859510794921873 : Rat) / 20000000000000000), LB := ((657245382383459 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50009632521 : Rat) / 20480000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((2376876279 : Rat) / 20480000000), D3 := ((10083241228027343819 : Rat) / 50000000000000000000), D4 := ((13704559482421871 : Rat) / 40000000000000000), LB := ((1810395011724239 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((50024441719 : Rat) / 20480000000), D0 := ((50024441719 : Rat) / 20480000000), D1 := ((12802551671 : Rat) / 20480000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10065163593750000069 : Rat) / 50000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((19840618161876683 : Rat) / 50000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50024441719 : Rat) / 20480000000), R := ((25015923159 : Rat) / 10240000000), D0 := ((25015923159 : Rat) / 10240000000), D1 := ((1280995627 : Rat) / 2048000000), D2 := ((2362067081 : Rat) / 20480000000), D3 := ((10047085959472656319 : Rat) / 50000000000000000000), D4 := ((13675635267578121 : Rat) / 40000000000000000), LB := ((541032463813023 : Rat) / 1250000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25015923159 : Rat) / 10240000000), R := ((50039250917 : Rat) / 20480000000), D0 := ((50039250917 : Rat) / 20480000000), D1 := ((12817360869 : Rat) / 20480000000), D2 := ((1177331241 : Rat) / 10240000000), D3 := ((10029008325195312569 : Rat) / 50000000000000000000), D4 := ((6830586580078123 : Rat) / 20000000000000000), LB := ((4701230418123481 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50039250917 : Rat) / 20480000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((2347257883 : Rat) / 20480000000), D3 := ((10010930690917968819 : Rat) / 50000000000000000000), D4 := ((13646711052734371 : Rat) / 40000000000000000), LB := ((508706810528281 : Rat) / 1000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((10010812023 : Rat) / 4096000000), D0 := ((10010812023 : Rat) / 4096000000), D1 := ((12832170067 : Rat) / 20480000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((9992853056640625069 : Rat) / 50000000000000000000), D4 := ((852015559082031 : Rat) / 2500000000000000), LB := ((342862832067789 : Rat) / 625000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((10010812023 : Rat) / 4096000000), R := ((25030732357 : Rat) / 10240000000), D0 := ((25030732357 : Rat) / 10240000000), D1 := ((6419787333 : Rat) / 10240000000), D2 := ((466489737 : Rat) / 4096000000), D3 := ((9974775422363281319 : Rat) / 50000000000000000000), D4 := ((13617786837890621 : Rat) / 40000000000000000), LB := ((5897474775039963 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25030732357 : Rat) / 10240000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((1162522043 : Rat) / 10240000000), D3 := ((9956697788085937569 : Rat) / 50000000000000000000), D4 := ((6801662365234373 : Rat) / 20000000000000000), LB := ((404583534665149 : Rat) / 6250000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((5009108311 : Rat) / 2048000000), D0 := ((5009108311 : Rat) / 2048000000), D1 := ((6434596531 : Rat) / 10240000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((9920542519531250069 : Rat) / 50000000000000000000), D4 := ((3393600128906249 : Rat) / 10000000000000000), LB := ((15408983273314247 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5009108311 : Rat) / 2048000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((229542569 : Rat) / 2048000000), D3 := ((9884387250976562569 : Rat) / 50000000000000000000), D4 := ((6772738150390623 : Rat) / 20000000000000000), LB := ((24867123881015807 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((25060350753 : Rat) / 10240000000), D0 := ((25060350753 : Rat) / 10240000000), D1 := ((6449405729 : Rat) / 10240000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((9848231982421875069 : Rat) / 50000000000000000000), D4 := ((1689569010742187 : Rat) / 5000000000000000), LB := ((6970092811514339 : Rat) / 20000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25060350753 : Rat) / 10240000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((1132903647 : Rat) / 10240000000), D3 := ((9812076713867187569 : Rat) / 50000000000000000000), D4 := ((6743813935546873 : Rat) / 20000000000000000), LB := ((4536174179260999 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((25075159951 : Rat) / 10240000000), D0 := ((25075159951 : Rat) / 10240000000), D1 := ((6464214927 : Rat) / 10240000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((9775921445312500069 : Rat) / 50000000000000000000), D4 := ((3364675914062499 : Rat) / 10000000000000000), LB := ((2820186392034421 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25075159951 : Rat) / 10240000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((1118094449 : Rat) / 10240000000), D3 := ((9739766176757812569 : Rat) / 50000000000000000000), D4 := ((6714889720703123 : Rat) / 20000000000000000), LB := ((6797922618477503 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((501651291 : Rat) / 204800000), R := ((25089969149 : Rat) / 10240000000), D0 := ((25089969149 : Rat) / 10240000000), D1 := ((51832193 : Rat) / 81920000), D2 := ((22213797 : Rat) / 204800000), D3 := ((9703610908203125069 : Rat) / 50000000000000000000), D4 := ((209388362915039 : Rat) / 625000000000000), LB := ((4004553725446419 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25089969149 : Rat) / 10240000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((1103285251 : Rat) / 10240000000), D3 := ((9667455639648437569 : Rat) / 50000000000000000000), D4 := ((6685965505859373 : Rat) / 20000000000000000), LB := ((9274214467912267 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((25104778347 : Rat) / 10240000000), D0 := ((25104778347 : Rat) / 10240000000), D1 := ((6493833323 : Rat) / 10240000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((9631300371093750069 : Rat) / 50000000000000000000), D4 := ((3335751699218749 : Rat) / 10000000000000000), LB := ((10593534323359993 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25104778347 : Rat) / 10240000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((1088476053 : Rat) / 10240000000), D3 := ((9595145102539062569 : Rat) / 50000000000000000000), D4 := ((6657041291015623 : Rat) / 20000000000000000), LB := ((93495009282987 : Rat) / 78125000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((9558989833984375069 : Rat) / 50000000000000000000), D4 := ((1660644795898437 : Rat) / 5000000000000000), LB := ((21687988638362243 : Rat) / 100000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9486679296875000069 : Rat) / 50000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((2606103827150069 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((9414368759765625069 : Rat) / 50000000000000000000), D4 := ((823091344238281 : Rat) / 2500000000000000), LB := ((1059801589751077 : Rat) / 1250000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((12585709869 : Rat) / 5120000000), D0 := ((12585709869 : Rat) / 5120000000), D1 := ((3280237357 : Rat) / 5120000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9342058222656250069 : Rat) / 50000000000000000000), D4 := ((3277903269531249 : Rat) / 10000000000000000), LB := ((2992482603532999 : Rat) / 2500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12585709869 : Rat) / 5120000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((510917331 : Rat) / 5120000000), D3 := ((9269747685546875069 : Rat) / 50000000000000000000), D4 := ((1631720581054687 : Rat) / 5000000000000000), LB := ((313786788303419 : Rat) / 200000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((12600519067 : Rat) / 5120000000), D0 := ((12600519067 : Rat) / 5120000000), D1 := ((659009311 : Rat) / 1024000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9197437148437500069 : Rat) / 50000000000000000000), D4 := ((3248979054687499 : Rat) / 10000000000000000), LB := ((981964129253353 : Rat) / 500000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12600519067 : Rat) / 5120000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((496108133 : Rat) / 5120000000), D3 := ((9125126611328125069 : Rat) / 50000000000000000000), D4 := ((404314618408203 : Rat) / 1250000000000000), LB := ((297780861640359 : Rat) / 125000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9052816074218750069 : Rat) / 50000000000000000000), D4 := ((3220054839843749 : Rat) / 10000000000000000), LB := ((1220175618093261 : Rat) / 2000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((8908195000000000069 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((98363112395773 : Rat) / 62500000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((8763573925781250069 : Rat) / 50000000000000000000), D4 := ((3162206410156249 : Rat) / 10000000000000000), LB := ((13176933675874969 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((8618952851562500069 : Rat) / 50000000000000000000), D4 := ((3133282195312499 : Rat) / 10000000000000000), LB := ((37973093111157707 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((8474331777343750069 : Rat) / 50000000000000000000), D4 := ((3104357980468749 : Rat) / 10000000000000000), LB := ((202487992498237 : Rat) / 40000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8329710703125000069 : Rat) / 50000000000000000000), D4 := ((3075433765624999 : Rat) / 10000000000000000), LB := ((20940659216237417 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8040468554687500069 : Rat) / 50000000000000000000), D4 := ((3017585335937499 : Rat) / 10000000000000000), LB := ((5194435329407651 : Rat) / 1000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((7751226406250000069 : Rat) / 50000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((1200952038261649 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7172742109375000069 : Rat) / 50000000000000000000), D4 := ((2844040046874999 : Rat) / 10000000000000000), LB := ((1793905625711223 : Rat) / 200000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6594257812500000069 : Rat) / 50000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((438061007798099 : Rat) / 125000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5437289218750000069 : Rat) / 50000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((424683062757867 : Rat) / 12500000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((260073820625000000069 : Rat) / 100000000000000000000), D0 := ((260073820625000000069 : Rat) / 100000000000000000000), D1 := ((78326310625000000069 : Rat) / 100000000000000000000), D2 := ((4280320625000000069 : Rat) / 100000000000000000000), D3 := ((4280320625000000069 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((2651733059362417 : Rat) / 50000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((260073820625000000069 : Rat) / 100000000000000000000), R := ((132177070625000000069 : Rat) / 50000000000000000000), D0 := ((132177070625000000069 : Rat) / 50000000000000000000), D1 := ((41303315625000000069 : Rat) / 50000000000000000000), D2 := ((4280320625000000069 : Rat) / 50000000000000000000), D3 := ((4280320625000000069 : Rat) / 100000000000000000000), D4 := ((18375236874999989931 : Rat) / 100000000000000000000), LB := ((4264808775028519 : Rat) / 20000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((132177070625000000069 : Rat) / 50000000000000000000), R := ((33634072165178571459 : Rat) / 12500000000000000000), D0 := ((33634072165178571459 : Rat) / 12500000000000000000), D1 := ((10915633415178571459 : Rat) / 12500000000000000000), D2 := ((1659884665178571459 : Rat) / 12500000000000000000), D3 := ((2359218035714285767 : Rat) / 50000000000000000000), D4 := ((7047458124999994931 : Rat) / 50000000000000000000), LB := ((473886574250083 : Rat) / 3125000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33634072165178571459 : Rat) / 12500000000000000000), R := ((271431795357142857439 : Rat) / 100000000000000000000), D0 := ((271431795357142857439 : Rat) / 100000000000000000000), D1 := ((89684285357142857439 : Rat) / 100000000000000000000), D2 := ((15638295357142857439 : Rat) / 100000000000000000000), D3 := ((7077654107142857301 : Rat) / 100000000000000000000), D4 := ((1172060022321427291 : Rat) / 12500000000000000000), LB := ((4581173822586923 : Rat) / 100000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((271431795357142857439 : Rat) / 100000000000000000000), R := ((109044561750000000129 : Rat) / 40000000000000000000), D0 := ((109044561750000000129 : Rat) / 40000000000000000000), D1 := ((36345557750000000129 : Rat) / 40000000000000000000), D2 := ((6727161750000000129 : Rat) / 40000000000000000000), D3 := ((16514526250000000369 : Rat) / 200000000000000000000), D4 := ((7017262142857132561 : Rat) / 100000000000000000000), LB := ((14696027178459331 : Rat) / 1000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((109044561750000000129 : Rat) / 40000000000000000000), R := ((1092804835535714287057 : Rat) / 400000000000000000000), D0 := ((1092804835535714287057 : Rat) / 400000000000000000000), D1 := ((365814795535714287057 : Rat) / 400000000000000000000), D2 := ((69630835535714287057 : Rat) / 400000000000000000000), D3 := ((7077654107142857301 : Rat) / 80000000000000000000), D4 := ((2335061249999995871 : Rat) / 40000000000000000000), LB := ((630016582713333 : Rat) / 125000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1092804835535714287057 : Rat) / 400000000000000000000), R := ((2187968889107142859881 : Rat) / 800000000000000000000), D0 := ((2187968889107142859881 : Rat) / 800000000000000000000), D1 := ((733988809107142859881 : Rat) / 800000000000000000000), D2 := ((141620889107142859881 : Rat) / 800000000000000000000), D3 := ((73135759107142858777 : Rat) / 800000000000000000000), D4 := ((20991394464285672943 : Rat) / 400000000000000000000), LB := ((2026876471957151 : Rat) / 1000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2187968889107142859881 : Rat) / 800000000000000000000), R := ((4378296996250000005529 : Rat) / 1600000000000000000000), D0 := ((4378296996250000005529 : Rat) / 1600000000000000000000), D1 := ((1470336836250000005529 : Rat) / 1600000000000000000000), D2 := ((285600996250000005529 : Rat) / 1600000000000000000000), D3 := ((148630736250000003321 : Rat) / 1600000000000000000000), D4 := ((39623570892857060119 : Rat) / 800000000000000000000), LB := ((5260026576938137 : Rat) / 5000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4378296996250000005529 : Rat) / 1600000000000000000000), R := ((350358128421428571873 : Rat) / 128000000000000000000), D0 := ((350358128421428571873 : Rat) / 128000000000000000000), D1 := ((117721315621428571873 : Rat) / 128000000000000000000), D2 := ((22942448421428571873 : Rat) / 128000000000000000000), D3 := ((299620690535714292409 : Rat) / 3200000000000000000000), D4 := ((76887923749999834471 : Rat) / 1600000000000000000000), LB := ((7110019793423183 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((350358128421428571873 : Rat) / 128000000000000000000), R := ((17520265639107142879417 : Rat) / 6400000000000000000000), D0 := ((17520265639107142879417 : Rat) / 6400000000000000000000), D1 := ((5888424999107142879417 : Rat) / 6400000000000000000000), D2 := ((1149481639107142879417 : Rat) / 6400000000000000000000), D3 := ((120320119821428574117 : Rat) / 1280000000000000000000), D4 := ((6056665178571415327 : Rat) / 128000000000000000000), LB := ((5791130854409521 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17520265639107142879417 : Rat) / 6400000000000000000000), R := ((35042890496250000044601 : Rat) / 12800000000000000000000), D0 := ((35042890496250000044601 : Rat) / 12800000000000000000000), D1 := ((11779209216250000044601 : Rat) / 12800000000000000000000), D2 := ((2301322496250000044601 : Rat) / 12800000000000000000000), D3 := ((1205560416250000026937 : Rat) / 12800000000000000000000), D4 := ((300474040892856480583 : Rat) / 6400000000000000000000), LB := ((5230960331051859 : Rat) / 10000000000000000000) },
  { w1 := ((291286471583419 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := ((5661722292537289 : Rat) / 20000000000000000), w4 := ((9099907830316023 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132177070625000000069 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35042890496250000044601 : Rat) / 12800000000000000000000), R := ((136895506696428571603 : Rat) / 50000000000000000000), D0 := ((136895506696428571603 : Rat) / 50000000000000000000), D1 := ((46021751696428571603 : Rat) / 50000000000000000000), D2 := ((8998756696428571603 : Rat) / 50000000000000000000), D3 := ((2359218035714285767 : Rat) / 25000000000000000000), D4 := ((598588863749998675399 : Rat) / 12800000000000000000000), LB := ((5722184902540173 : Rat) / 50000000000000000000) }
]

def block407RightChunk001L : Rat := ((99760104077 : Rat) / 40960000000)
def block407RightChunk001R : Rat := ((136895506696428571603 : Rat) / 50000000000000000000)

def block407RightChunk001Certificate : Bool :=
  allBoxesValid block407RightChunk001 &&
  coversFromBool block407RightChunk001 block407RightChunk001L block407RightChunk001R

theorem block407RightChunk001Certificate_eq_true :
    block407RightChunk001Certificate = true := by
  native_decide

def block407RightChainCertificate : Bool :=
  decide (
    block407RightL = ((10860716517857142879 : Rat) / 6250000000000000000) /\
    ((99760104077 : Rat) / 40960000000) = ((99760104077 : Rat) / 40960000000) /\
    ((136895506696428571603 : Rat) / 50000000000000000000) = block407RightR)

theorem block407RightChainCertificate_eq_true :
    block407RightChainCertificate = true := by
  native_decide

def block407LeftBoxCount : Nat := boxCount block407LeftBoxes
def block407RightBoxCount : Nat := 169

def block407_rational_certificate : Prop :=
    block407LeftCertificate = true /\
    block407RightChainCertificate = true /\
    block407RightChunk000Certificate = true /\
    block407RightChunk001Certificate = true

theorem block407_rational_certificate_proof :
    block407_rational_certificate := by
  exact ⟨block407LeftCertificate_eq_true, block407RightChainCertificate_eq_true, block407RightChunk000Certificate_eq_true, block407RightChunk001Certificate_eq_true⟩

end Block407
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block407

open Set

def block407W1 : Rat := ((291286471583419 : Rat) / 400000000000000)
def block407W2 : Rat := (0 : Rat)
def block407W3 : Rat := ((5661722292537289 : Rat) / 20000000000000000)
def block407W4 : Rat := ((9099907830316023 : Rat) / 100000000000000000)
def block407S1 : Rat := ((18174751 : Rat) / 10000000)
def block407S2 : Rat := ((511587 : Rat) / 200000)
def block407S3 : Rat := ((132177070625000000069 : Rat) / 50000000000000000000)
def block407S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block407V (y : ℝ) : ℝ :=
  ratPotential block407W1 block407W2 block407W3 block407W4 block407S1 block407S2 block407S3 block407S4 y

def block407LeftParamsCertificate : Bool :=
  allBoxesSameParams block407LeftBoxes block407W1 block407W2 block407W3 block407W4 block407S1 block407S2 block407S3 block407S4

theorem block407LeftParamsCertificate_eq_true :
    block407LeftParamsCertificate = true := by
  native_decide

theorem block407_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block407LeftL : ℝ) (block407LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block407S1 : ℝ))
    (hy2ne : y ≠ (block407S2 : ℝ))
    (hy3ne : y ≠ (block407S3 : ℝ))
    (hy4ne : y ≠ (block407S4 : ℝ)) :
    0 < block407V y := by
  have hcert := block407LeftCertificate_eq_true
  unfold block407LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block407LeftBoxes) (lo := block407LeftL) (hi := block407LeftR)
    (w1 := block407W1) (w2 := block407W2) (w3 := block407W3) (w4 := block407W4)
    (s1 := block407S1) (s2 := block407S2) (s3 := block407S3) (s4 := block407S4)
    hboxes hcover block407LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block407RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block407RightChunk000 block407W1 block407W2 block407W3 block407W4 block407S1 block407S2 block407S3 block407S4

theorem block407RightChunk000ParamsCertificate_eq_true :
    block407RightChunk000ParamsCertificate = true := by
  native_decide

theorem block407_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block407RightChunk000L : ℝ) (block407RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block407S1 : ℝ))
    (hy2ne : y ≠ (block407S2 : ℝ))
    (hy3ne : y ≠ (block407S3 : ℝ))
    (hy4ne : y ≠ (block407S4 : ℝ)) :
    0 < block407V y := by
  have hcert := block407RightChunk000Certificate_eq_true
  unfold block407RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block407RightChunk000) (lo := block407RightChunk000L) (hi := block407RightChunk000R)
    (w1 := block407W1) (w2 := block407W2) (w3 := block407W3) (w4 := block407W4)
    (s1 := block407S1) (s2 := block407S2) (s3 := block407S3) (s4 := block407S4)
    hboxes hcover block407RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block407RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block407RightChunk001 block407W1 block407W2 block407W3 block407W4 block407S1 block407S2 block407S3 block407S4

theorem block407RightChunk001ParamsCertificate_eq_true :
    block407RightChunk001ParamsCertificate = true := by
  native_decide

theorem block407_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block407RightChunk001L : ℝ) (block407RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block407S1 : ℝ))
    (hy2ne : y ≠ (block407S2 : ℝ))
    (hy3ne : y ≠ (block407S3 : ℝ))
    (hy4ne : y ≠ (block407S4 : ℝ)) :
    0 < block407V y := by
  have hcert := block407RightChunk001Certificate_eq_true
  unfold block407RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block407RightChunk001) (lo := block407RightChunk001L) (hi := block407RightChunk001R)
    (w1 := block407W1) (w2 := block407W2) (w3 := block407W3) (w4 := block407W4)
    (s1 := block407S1) (s2 := block407S2) (s3 := block407S3) (s4 := block407S4)
    hboxes hcover block407RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block407_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block407RightL : ℝ) (block407RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block407S1 : ℝ))
    (hy2ne : y ≠ (block407S2 : ℝ))
    (hy3ne : y ≠ (block407S3 : ℝ))
    (hy4ne : y ≠ (block407S4 : ℝ)) :
    0 < block407V y := by
  by_cases h0 : y ≤ (block407RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block407RightChunk000L : ℝ) (block407RightChunk000R : ℝ) := by
      have hL : (block407RightChunk000L : ℝ) = (block407RightL : ℝ) := by
        norm_num [block407RightChunk000L, block407RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block407_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block407RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block407RightChunk001L : ℝ) = (block407RightChunk000R : ℝ) := by
      norm_num [block407RightChunk001L, block407RightChunk000R]
    have hR : (block407RightChunk001R : ℝ) = (block407RightR : ℝ) := by
      norm_num [block407RightChunk001R, block407RightR]
    have hyc : y ∈ Icc (block407RightChunk001L : ℝ) (block407RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block407_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block407_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block407LeftL : ℝ) (block407LeftR : ℝ) →
    y ≠ 0 → y ≠ (block407S1 : ℝ) → y ≠ (block407S2 : ℝ) →
    y ≠ (block407S3 : ℝ) → y ≠ (block407S4 : ℝ) → 0 < block407V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block407RightL : ℝ) (block407RightR : ℝ) →
    y ≠ 0 → y ≠ (block407S1 : ℝ) → y ≠ (block407S2 : ℝ) →
    y ≠ (block407S3 : ℝ) → y ≠ (block407S4 : ℝ) → 0 < block407V y)

theorem block407_reallog_certificate_proof :
    block407_reallog_certificate := by
  exact ⟨block407_left_V_pos, block407_right_V_pos⟩

end Block407
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block407.block407V
#check Erdos1038Lean.M1817475.Block407.block407_left_V_pos
#check Erdos1038Lean.M1817475.Block407.block407_right_V_pos
#check Erdos1038Lean.M1817475.Block407.block407_reallog_certificate_proof
