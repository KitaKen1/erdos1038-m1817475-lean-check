/-
Self-contained Lean4Web paste file.
Block 282 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block282

def block282LeftL : Rat := ((38107551339285714407 : Rat) / 50000000000000000000)
def block282LeftR : Rat := ((19058662946428571489 : Rat) / 25000000000000000000)
def block282RightL : Rat := ((88107551339285714407 : Rat) / 50000000000000000000)
def block282RightR : Rat := ((69058662946428571489 : Rat) / 25000000000000000000)

def block282LeftBoxes : List RatBox := [
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((38107551339285714407 : Rat) / 50000000000000000000), R := ((19058662946428571489 : Rat) / 25000000000000000000), D0 := ((19058662946428571489 : Rat) / 25000000000000000000), D1 := ((52766203660714285593 : Rat) / 50000000000000000000), D2 := ((89789198660714285593 : Rat) / 50000000000000000000), D3 := ((48970121249999999889 : Rat) / 25000000000000000000), D4 := ((20344599946428570399 : Rat) / 10000000000000000000), LB := ((2129238145449047 : Rat) / 500000000000000000) }
]

def block282LeftCertificate : Bool :=
  allBoxesValid block282LeftBoxes &&
  coversFromBool block282LeftBoxes block282LeftL block282LeftR

theorem block282LeftCertificate_eq_true :
    block282LeftCertificate = true := by
  native_decide

def block282RightChunk000 : List RatBox := [
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((88107551339285714407 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((2766203660714285593 : Rat) / 50000000000000000000), D2 := ((39789198660714285593 : Rat) / 50000000000000000000), D3 := ((23970121249999999889 : Rat) / 25000000000000000000), D4 := ((10344599946428570399 : Rat) / 10000000000000000000), LB := ((300102583762339 : Rat) / 125000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((24478398035714283201 : Rat) / 25000000000000000000), LB := ((174244381494207 : Rat) / 625000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((15222649285714283201 : Rat) / 25000000000000000000), LB := ((908728442962111 : Rat) / 5000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((4406933392857142837 : Rat) / 10000000000000000000), D4 := ((12908712098214283201 : Rat) / 25000000000000000000), LB := ((18530755916785907 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((10594774910714283201 : Rat) / 25000000000000000000), LB := ((9577603933452461 : Rat) / 200000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((3249964799107142837 : Rat) / 10000000000000000000), D4 := ((10016290613839283201 : Rat) / 25000000000000000000), LB := ((22089796042973453 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((3018571080357142837 : Rat) / 10000000000000000000), D4 := ((9437806316964283201 : Rat) / 25000000000000000000), LB := ((29880336707782673 : Rat) / 500000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2787177361607142837 : Rat) / 10000000000000000000), D4 := ((8859322020089283201 : Rat) / 25000000000000000000), LB := ((338721071413417 : Rat) / 62500000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2671480502232142837 : Rat) / 10000000000000000000), D4 := ((8570079871651783201 : Rat) / 25000000000000000000), LB := ((4719779034402627 : Rat) / 500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2613632072544642837 : Rat) / 10000000000000000000), D4 := ((8425458797433033201 : Rat) / 25000000000000000000), LB := ((6055906526921173 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((8280837723214283201 : Rat) / 25000000000000000000), LB := ((6035832753684911 : Rat) / 2000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((2497935213169642837 : Rat) / 10000000000000000000), D4 := ((8136216648995533201 : Rat) / 25000000000000000000), LB := ((8645213122165929 : Rat) / 25000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((2440086783482142837 : Rat) / 10000000000000000000), D4 := ((7991595574776783201 : Rat) / 25000000000000000000), LB := ((37127959184624637 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((2411162568638392837 : Rat) / 10000000000000000000), D4 := ((7919285037667408201 : Rat) / 25000000000000000000), LB := ((1352834663148339 : Rat) / 500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((2382238353794642837 : Rat) / 10000000000000000000), D4 := ((7846974500558033201 : Rat) / 25000000000000000000), LB := ((4518195931713237 : Rat) / 2500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((2353314138950892837 : Rat) / 10000000000000000000), D4 := ((7774663963448658201 : Rat) / 25000000000000000000), LB := ((10221338135917857 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((2324389924107142837 : Rat) / 10000000000000000000), D4 := ((7702353426339283201 : Rat) / 25000000000000000000), LB := ((710473129783673 : Rat) / 2000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((2552684049 : Rat) / 1024000000), D0 := ((2552684049 : Rat) / 1024000000), D1 := ((3457947733 : Rat) / 5120000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((2295465709263392837 : Rat) / 10000000000000000000), D4 := ((7630042889229908201 : Rat) / 25000000000000000000), LB := ((648296886962399 : Rat) / 250000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((2552684049 : Rat) / 1024000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 1024000000), D3 := ((2281003601841517837 : Rat) / 10000000000000000000), D4 := ((7593887620675220701 : Rat) / 25000000000000000000), LB := ((2364963722673863 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((12778229443 : Rat) / 5120000000), D0 := ((12778229443 : Rat) / 5120000000), D1 := ((3472756931 : Rat) / 5120000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((2266541494419642837 : Rat) / 10000000000000000000), D4 := ((7557732352120533201 : Rat) / 25000000000000000000), LB := ((1085055203120161 : Rat) / 500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12778229443 : Rat) / 5120000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((318397757 : Rat) / 5120000000), D3 := ((2252079386997767837 : Rat) / 10000000000000000000), D4 := ((7521577083565845701 : Rat) / 25000000000000000000), LB := ((156994523102757 : Rat) / 78125000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((12793038641 : Rat) / 5120000000), D0 := ((12793038641 : Rat) / 5120000000), D1 := ((3487566129 : Rat) / 5120000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((2237617279575892837 : Rat) / 10000000000000000000), D4 := ((7485421815011158201 : Rat) / 25000000000000000000), LB := ((18841822366548189 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12793038641 : Rat) / 5120000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((303588559 : Rat) / 5120000000), D3 := ((2223155172154017837 : Rat) / 10000000000000000000), D4 := ((7449266546456470701 : Rat) / 25000000000000000000), LB := ((17950905770977577 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((12807847839 : Rat) / 5120000000), D0 := ((12807847839 : Rat) / 5120000000), D1 := ((3502375327 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((2208693064732142837 : Rat) / 10000000000000000000), D4 := ((7413111277901783201 : Rat) / 25000000000000000000), LB := ((8716735881585669 : Rat) / 5000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12807847839 : Rat) / 5120000000), R := ((6407626219 : Rat) / 2560000000), D0 := ((6407626219 : Rat) / 2560000000), D1 := ((1754889963 : Rat) / 2560000000), D2 := ((288779361 : Rat) / 5120000000), D3 := ((2194230957310267837 : Rat) / 10000000000000000000), D4 := ((7376956009347095701 : Rat) / 25000000000000000000), LB := ((4325300418565603 : Rat) / 2500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6407626219 : Rat) / 2560000000), R := ((12822657037 : Rat) / 5120000000), D0 := ((12822657037 : Rat) / 5120000000), D1 := ((140687381 : Rat) / 204800000), D2 := ((140687381 : Rat) / 2560000000), D3 := ((2179768849888392837 : Rat) / 10000000000000000000), D4 := ((7340800740792408201 : Rat) / 25000000000000000000), LB := ((17566611910739827 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12822657037 : Rat) / 5120000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((273970163 : Rat) / 5120000000), D3 := ((2165306742466517837 : Rat) / 10000000000000000000), D4 := ((7304645472237720701 : Rat) / 25000000000000000000), LB := ((18243140393500723 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((2567493247 : Rat) / 1024000000), D0 := ((2567493247 : Rat) / 1024000000), D1 := ((3531993723 : Rat) / 5120000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((2150844635044642837 : Rat) / 10000000000000000000), D4 := ((7268490203683033201 : Rat) / 25000000000000000000), LB := ((19345244756794333 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((2567493247 : Rat) / 1024000000), R := ((6422435417 : Rat) / 2560000000), D0 := ((6422435417 : Rat) / 2560000000), D1 := ((1769699161 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 1024000000), D3 := ((2136382527622767837 : Rat) / 10000000000000000000), D4 := ((7232334935128345701 : Rat) / 25000000000000000000), LB := ((652766071625923 : Rat) / 312500000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6422435417 : Rat) / 2560000000), R := ((12852275433 : Rat) / 5120000000), D0 := ((12852275433 : Rat) / 5120000000), D1 := ((3546802921 : Rat) / 5120000000), D2 := ((125878183 : Rat) / 2560000000), D3 := ((2121920420200892837 : Rat) / 10000000000000000000), D4 := ((7196179666573658201 : Rat) / 25000000000000000000), LB := ((22889798023906227 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12852275433 : Rat) / 5120000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((244351767 : Rat) / 5120000000), D3 := ((2107458312779017837 : Rat) / 10000000000000000000), D4 := ((7160024398018970701 : Rat) / 25000000000000000000), LB := ((634183795136023 : Rat) / 250000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1287448923 : Rat) / 512000000), D0 := ((1287448923 : Rat) / 512000000), D1 := ((1784508359 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((7123869129464283201 : Rat) / 25000000000000000000), LB := ((12173836373813307 : Rat) / 100000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1287448923 : Rat) / 512000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 512000000), D3 := ((2064071990513392837 : Rat) / 10000000000000000000), D4 := ((7051558592354908201 : Rat) / 25000000000000000000), LB := ((2209109161418199 : Rat) / 2500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((6452053813 : Rat) / 2560000000), D0 := ((6452053813 : Rat) / 2560000000), D1 := ((1799317557 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((2035147775669642837 : Rat) / 10000000000000000000), D4 := ((6979248055245533201 : Rat) / 25000000000000000000), LB := ((468152146287093 : Rat) / 250000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6452053813 : Rat) / 2560000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((96259787 : Rat) / 2560000000), D3 := ((2006223560825892837 : Rat) / 10000000000000000000), D4 := ((6906937518136158201 : Rat) / 25000000000000000000), LB := ((1556331277589279 : Rat) / 500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((6466863011 : Rat) / 2560000000), D0 := ((6466863011 : Rat) / 2560000000), D1 := ((362825351 : Rat) / 512000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1977299345982142837 : Rat) / 10000000000000000000), D4 := ((6834626981026783201 : Rat) / 25000000000000000000), LB := ((1158333683082713 : Rat) / 250000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6466863011 : Rat) / 2560000000), R := ((647426761 : Rat) / 256000000), D0 := ((647426761 : Rat) / 256000000), D1 := ((910765677 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 2560000000), D3 := ((1948375131138392837 : Rat) / 10000000000000000000), D4 := ((6762316443917408201 : Rat) / 25000000000000000000), LB := ((1294310251200359 : Rat) / 200000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((647426761 : Rat) / 256000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 256000000), D3 := ((1919450916294642837 : Rat) / 10000000000000000000), D4 := ((6690005906808033201 : Rat) / 25000000000000000000), LB := ((3375142851126889 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((3251943003 : Rat) / 1280000000), D0 := ((3251943003 : Rat) / 1280000000), D1 := ((7404599 : Rat) / 10240000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((6545384832589283201 : Rat) / 25000000000000000000), LB := ((9178573762460507 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3251943003 : Rat) / 1280000000), R := ((1629673801 : Rat) / 640000000), D0 := ((1629673801 : Rat) / 640000000), D1 := ((466489737 : Rat) / 640000000), D2 := ((22213797 : Rat) / 1280000000), D3 := ((1803754056919642837 : Rat) / 10000000000000000000), D4 := ((6400763758370533201 : Rat) / 25000000000000000000), LB := ((17533282207986167 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1629673801 : Rat) / 640000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 640000000), D3 := ((1745905627232142837 : Rat) / 10000000000000000000), D4 := ((6256142684151783201 : Rat) / 25000000000000000000), LB := ((19936583097021787 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((410899808767857142837 : Rat) / 160000000000000000000), D0 := ((410899808767857142837 : Rat) / 160000000000000000000), D1 := ((120103792767857142837 : Rat) / 160000000000000000000), D2 := ((1630208767857142837 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((5966900535714283201 : Rat) / 25000000000000000000), LB := ((12891308497164189 : Rat) / 500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((410899808767857142837 : Rat) / 160000000000000000000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 32000000000000000000), D4 := ((182789773303571348247 : Rat) / 800000000000000000000), LB := ((335068417261733 : Rat) / 125000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((165338048767857142837 : Rat) / 64000000000000000000), D0 := ((165338048767857142837 : Rat) / 64000000000000000000), D1 := ((49019642367857142837 : Rat) / 64000000000000000000), D2 := ((1630208767857142837 : Rat) / 64000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((87319364732142817031 : Rat) / 400000000000000000000), LB := ((1177282977694527 : Rat) / 200000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((165338048767857142837 : Rat) / 64000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((44015636732142856599 : Rat) / 320000000000000000000), D4 := ((341126415089285553939 : Rat) / 1600000000000000000000), LB := ((12347235832718129 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((1658271113982142856881 : Rat) / 640000000000000000000), D0 := ((1658271113982142856881 : Rat) / 640000000000000000000), D1 := ((495087049982142856881 : Rat) / 640000000000000000000), D2 := ((21192713982142856881 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((166487685624999919877 : Rat) / 800000000000000000000), LB := ((9765391341335139 : Rat) / 2000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1658271113982142856881 : Rat) / 640000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((83140647160714284687 : Rat) / 640000000000000000000), D4 := ((657799698660713965323 : Rat) / 3200000000000000000000), LB := ((1408717231439649 : Rat) / 400000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((332306306303571428511 : Rat) / 128000000000000000000), D0 := ((332306306303571428511 : Rat) / 128000000000000000000), D1 := ((99669493503571428511 : Rat) / 128000000000000000000), D2 := ((4890626303571428511 : Rat) / 128000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((324824327410714125569 : Rat) / 1600000000000000000000), LB := ((2457324631632951 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((332306306303571428511 : Rat) / 128000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((79880229624999999013 : Rat) / 640000000000000000000), D4 := ((641497610982142536953 : Rat) / 3200000000000000000000), LB := ((8355361952518403 : Rat) / 5000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((1664791949053571428229 : Rat) / 640000000000000000000), D0 := ((1664791949053571428229 : Rat) / 640000000000000000000), D1 := ((501607885053571428229 : Rat) / 640000000000000000000), D2 := ((27713549053571428229 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((39584160446428551423 : Rat) / 200000000000000000000), LB := ((287300769681309 : Rat) / 250000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1664791949053571428229 : Rat) / 640000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((76619812089285713339 : Rat) / 640000000000000000000), D4 := ((625195523303571108583 : Rat) / 3200000000000000000000), LB := ((8813502991396049 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((308522239732142697199 : Rat) / 1600000000000000000000), LB := ((8599539530793621 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((608893435624999680213 : Rat) / 3200000000000000000000), LB := ((10797786705307733 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((150185597946428491507 : Rat) / 800000000000000000000), LB := ((15375599744815727 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((592591347946428251843 : Rat) / 3200000000000000000000), LB := ((22317438111448817 : Rat) / 10000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((292220152053571268829 : Rat) / 1600000000000000000000), LB := ((158114799831649 : Rat) / 50000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((576289260267856823473 : Rat) / 3200000000000000000000), LB := ((4330565364978889 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((71017277053571388661 : Rat) / 400000000000000000000), LB := ((17381624738943557 : Rat) / 100000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((275918064374999840459 : Rat) / 1600000000000000000000), LB := ((3848598988001939 : Rat) / 1000000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((133883510267857063137 : Rat) / 800000000000000000000), LB := ((4266635869678903 : Rat) / 500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((259615976696428412089 : Rat) / 1600000000000000000000), LB := ((1429519615240471 : Rat) / 100000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((15716558303571418619 : Rat) / 100000000000000000000), LB := ((689141673708947 : Rat) / 62500000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((117581422589285634767 : Rat) / 800000000000000000000), LB := ((14568416652446903 : Rat) / 500000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((54715189374999960291 : Rat) / 400000000000000000000), LB := ((692569555635909 : Rat) / 20000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((23282072767857123053 : Rat) / 200000000000000000000), LB := ((3890596920651923 : Rat) / 50000000000000000) },
  { w1 := ((10289938628935629 : Rat) / 10000000000000000), w2 := ((2135240267007591 : Rat) / 62500000000000000), w3 := ((14255218390878843 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((69058662946428571489 : Rat) / 25000000000000000000), D0 := ((69058662946428571489 : Rat) / 25000000000000000000), D1 := ((23621785446428571489 : Rat) / 25000000000000000000), D2 := ((5110287946428571489 : Rat) / 25000000000000000000), D3 := ((2069532053571428793 : Rat) / 50000000000000000000), D4 := ((3782757232142852217 : Rat) / 50000000000000000000), LB := ((1120320508710887 : Rat) / 250000000000000000) }
]

def block282RightChunk000L : Rat := ((88107551339285714407 : Rat) / 50000000000000000000)
def block282RightChunk000R : Rat := ((69058662946428571489 : Rat) / 25000000000000000000)

def block282RightChunk000Certificate : Bool :=
  allBoxesValid block282RightChunk000 &&
  coversFromBool block282RightChunk000 block282RightChunk000L block282RightChunk000R

theorem block282RightChunk000Certificate_eq_true :
    block282RightChunk000Certificate = true := by
  native_decide

def block282RightChainCertificate : Bool :=
  decide (
    block282RightL = ((88107551339285714407 : Rat) / 50000000000000000000) /\
    ((69058662946428571489 : Rat) / 25000000000000000000) = block282RightR)

theorem block282RightChainCertificate_eq_true :
    block282RightChainCertificate = true := by
  native_decide

def block282LeftBoxCount : Nat := boxCount block282LeftBoxes
def block282RightBoxCount : Nat := 66

def block282_rational_certificate : Prop :=
    block282LeftCertificate = true /\
    block282RightChainCertificate = true /\
    block282RightChunk000Certificate = true

theorem block282_rational_certificate_proof :
    block282_rational_certificate := by
  exact ⟨block282LeftCertificate_eq_true, block282RightChainCertificate_eq_true, block282RightChunk000Certificate_eq_true⟩

end Block282
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block282

open Set

def block282W1 : Rat := ((10289938628935629 : Rat) / 10000000000000000)
def block282W2 : Rat := ((2135240267007591 : Rat) / 62500000000000000)
def block282W3 : Rat := ((14255218390878843 : Rat) / 50000000000000000)
def block282W4 : Rat := (0 : Rat)
def block282S1 : Rat := ((18174751 : Rat) / 10000000)
def block282S2 : Rat := ((511587 : Rat) / 200000)
def block282S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block282S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block282V (y : ℝ) : ℝ :=
  ratPotential block282W1 block282W2 block282W3 block282W4 block282S1 block282S2 block282S3 block282S4 y

def block282LeftParamsCertificate : Bool :=
  allBoxesSameParams block282LeftBoxes block282W1 block282W2 block282W3 block282W4 block282S1 block282S2 block282S3 block282S4

theorem block282LeftParamsCertificate_eq_true :
    block282LeftParamsCertificate = true := by
  native_decide

theorem block282_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block282LeftL : ℝ) (block282LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block282S1 : ℝ))
    (hy2ne : y ≠ (block282S2 : ℝ))
    (hy3ne : y ≠ (block282S3 : ℝ))
    (hy4ne : y ≠ (block282S4 : ℝ)) :
    0 < block282V y := by
  have hcert := block282LeftCertificate_eq_true
  unfold block282LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block282LeftBoxes) (lo := block282LeftL) (hi := block282LeftR)
    (w1 := block282W1) (w2 := block282W2) (w3 := block282W3) (w4 := block282W4)
    (s1 := block282S1) (s2 := block282S2) (s3 := block282S3) (s4 := block282S4)
    hboxes hcover block282LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block282RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block282RightChunk000 block282W1 block282W2 block282W3 block282W4 block282S1 block282S2 block282S3 block282S4

theorem block282RightChunk000ParamsCertificate_eq_true :
    block282RightChunk000ParamsCertificate = true := by
  native_decide

theorem block282_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block282RightChunk000L : ℝ) (block282RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block282S1 : ℝ))
    (hy2ne : y ≠ (block282S2 : ℝ))
    (hy3ne : y ≠ (block282S3 : ℝ))
    (hy4ne : y ≠ (block282S4 : ℝ)) :
    0 < block282V y := by
  have hcert := block282RightChunk000Certificate_eq_true
  unfold block282RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block282RightChunk000) (lo := block282RightChunk000L) (hi := block282RightChunk000R)
    (w1 := block282W1) (w2 := block282W2) (w3 := block282W3) (w4 := block282W4)
    (s1 := block282S1) (s2 := block282S2) (s3 := block282S3) (s4 := block282S4)
    hboxes hcover block282RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block282_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block282RightL : ℝ) (block282RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block282S1 : ℝ))
    (hy2ne : y ≠ (block282S2 : ℝ))
    (hy3ne : y ≠ (block282S3 : ℝ))
    (hy4ne : y ≠ (block282S4 : ℝ)) :
    0 < block282V y := by
  have hL : (block282RightChunk000L : ℝ) = (block282RightL : ℝ) := by
    norm_num [block282RightChunk000L, block282RightL]
  have hR : (block282RightChunk000R : ℝ) = (block282RightR : ℝ) := by
    norm_num [block282RightChunk000R, block282RightR]
  have hyc : y ∈ Icc (block282RightChunk000L : ℝ) (block282RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block282_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block282_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block282LeftL : ℝ) (block282LeftR : ℝ) →
    y ≠ 0 → y ≠ (block282S1 : ℝ) → y ≠ (block282S2 : ℝ) →
    y ≠ (block282S3 : ℝ) → y ≠ (block282S4 : ℝ) → 0 < block282V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block282RightL : ℝ) (block282RightR : ℝ) →
    y ≠ 0 → y ≠ (block282S1 : ℝ) → y ≠ (block282S2 : ℝ) →
    y ≠ (block282S3 : ℝ) → y ≠ (block282S4 : ℝ) → 0 < block282V y)

theorem block282_reallog_certificate_proof :
    block282_reallog_certificate := by
  exact ⟨block282_left_V_pos, block282_right_V_pos⟩

end Block282
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block282.block282V
#check Erdos1038Lean.M1817475.Block282.block282_left_V_pos
#check Erdos1038Lean.M1817475.Block282.block282_right_V_pos
#check Erdos1038Lean.M1817475.Block282.block282_reallog_certificate_proof
