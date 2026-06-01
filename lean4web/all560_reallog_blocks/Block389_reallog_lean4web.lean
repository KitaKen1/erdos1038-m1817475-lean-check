/-
Self-contained Lean4Web paste file.
Block 389 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block389

def block389LeftL : Rat := ((3706167410714285731 : Rat) / 5000000000000000000)
def block389LeftR : Rat := ((37071448660714285881 : Rat) / 50000000000000000000)
def block389RightL : Rat := ((8706167410714285731 : Rat) / 5000000000000000000)
def block389RightR : Rat := ((137071448660714285881 : Rat) / 50000000000000000000)

def block389LeftBoxes : List RatBox := [
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3706167410714285731 : Rat) / 5000000000000000000), R := ((37071448660714285881 : Rat) / 50000000000000000000), D0 := ((37071448660714285881 : Rat) / 50000000000000000000), D1 := ((5381208089285714269 : Rat) / 5000000000000000000), D2 := ((9083507589285714269 : Rat) / 5000000000000000000), D3 := ((19093456089285714263 : Rat) / 10000000000000000000), D4 := ((51022779999999997419 : Rat) / 25000000000000000000), LB := ((247462883368201 : Rat) / 312500000000000000) }
]

def block389LeftCertificate : Bool :=
  allBoxesValid block389LeftBoxes &&
  coversFromBool block389LeftBoxes block389LeftL block389LeftR

theorem block389LeftCertificate_eq_true :
    block389LeftCertificate = true := by
  native_decide

def block389RightChunk000 : List RatBox := [
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8706167410714285731 : Rat) / 5000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((381208089285714269 : Rat) / 5000000000000000000), D2 := ((4083507589285714269 : Rat) / 5000000000000000000), D3 := ((9093456089285714263 : Rat) / 10000000000000000000), D4 := ((26022779999999997419 : Rat) / 25000000000000000000), LB := ((1877115177759057 : Rat) / 1250000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((333241596428571429 : Rat) / 400000000000000000), D4 := ((12058369776785713037 : Rat) / 12500000000000000000), LB := ((6910943600517923 : Rat) / 100000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((185149616428571429 : Rat) / 400000000000000000), D4 := ((7430495401785713037 : Rat) / 12500000000000000000), LB := ((93624461926953 : Rat) / 2000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((148126621428571429 : Rat) / 400000000000000000), D4 := ((6273526808035713037 : Rat) / 12500000000000000000), LB := ((6078790310197247 : Rat) / 250000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((129615123928571429 : Rat) / 400000000000000000), D4 := ((5695042511160713037 : Rat) / 12500000000000000000), LB := ((2290898485866391 : Rat) / 100000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((120359375178571429 : Rat) / 400000000000000000), D4 := ((5405800362723213037 : Rat) / 12500000000000000000), LB := ((3306095333732953 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((111103626428571429 : Rat) / 400000000000000000), D4 := ((5116558214285713037 : Rat) / 12500000000000000000), LB := ((8317050658264241 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((106475752053571429 : Rat) / 400000000000000000), D4 := ((4971937140066963037 : Rat) / 12500000000000000000), LB := ((12559427141518031 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((766707007 : Rat) / 320000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((101847877678571429 : Rat) / 400000000000000000), D4 := ((4827316065848213037 : Rat) / 12500000000000000000), LB := ((5541144022518679 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((99533940491071429 : Rat) / 400000000000000000), D4 := ((4755005528738838037 : Rat) / 12500000000000000000), LB := ((27980075847872377 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((97220003303571429 : Rat) / 400000000000000000), D4 := ((4682694991629463037 : Rat) / 12500000000000000000), LB := ((1605757709337713 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((123561673 : Rat) / 51200000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((94906066116071429 : Rat) / 400000000000000000), D4 := ((4610384454520088037 : Rat) / 12500000000000000000), LB := ((8026779279953697 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((93749097522321429 : Rat) / 400000000000000000), D4 := ((4574229185965400537 : Rat) / 12500000000000000000), LB := ((1097719145905493 : Rat) / 500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((387055803 : Rat) / 160000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((92592128928571429 : Rat) / 400000000000000000), D4 := ((4538073917410713037 : Rat) / 12500000000000000000), LB := ((2505262091585747 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((91435160334821429 : Rat) / 400000000000000000), D4 := ((4501918648856025537 : Rat) / 12500000000000000000), LB := ((1918173764187403 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((90278191741071429 : Rat) / 400000000000000000), D4 := ((4465763380301338037 : Rat) / 12500000000000000000), LB := ((21033705192848307 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((89699707444196429 : Rat) / 400000000000000000), D4 := ((4447685746023994287 : Rat) / 12500000000000000000), LB := ((17302755511595103 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((89121223147321429 : Rat) / 400000000000000000), D4 := ((4429608111746650537 : Rat) / 12500000000000000000), LB := ((13765825626394501 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((88542738850446429 : Rat) / 400000000000000000), D4 := ((4411530477469306787 : Rat) / 12500000000000000000), LB := ((5212468589895769 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((81450589 : Rat) / 640000000), D3 := ((87964254553571429 : Rat) / 400000000000000000), D4 := ((4393452843191963037 : Rat) / 12500000000000000000), LB := ((7282171887729727 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((87385770256696429 : Rat) / 400000000000000000), D4 := ((4375375208914619287 : Rat) / 12500000000000000000), LB := ((4339673780363873 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((86807285959821429 : Rat) / 400000000000000000), D4 := ((4357297574637275537 : Rat) / 12500000000000000000), LB := ((1999564450166913 : Rat) / 12500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((24941877169 : Rat) / 10240000000), D0 := ((24941877169 : Rat) / 10240000000), D1 := ((1266186429 : Rat) / 2048000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((86228801662946429 : Rat) / 400000000000000000), D4 := ((4339219940359931787 : Rat) / 12500000000000000000), LB := ((1148071928496197 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24941877169 : Rat) / 10240000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((1251377231 : Rat) / 10240000000), D3 := ((85939559514508929 : Rat) / 400000000000000000), D4 := ((541272640402657489 : Rat) / 1562500000000000000), LB := ((5139342177756939 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((24956686367 : Rat) / 10240000000), D0 := ((24956686367 : Rat) / 10240000000), D1 := ((6345741343 : Rat) / 10240000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((85650317366071429 : Rat) / 400000000000000000), D4 := ((4321142306082588037 : Rat) / 12500000000000000000), LB := ((365149952954813 : Rat) / 400000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24956686367 : Rat) / 10240000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((1236568033 : Rat) / 10240000000), D3 := ((85361075217633929 : Rat) / 400000000000000000), D4 := ((2156051744471958081 : Rat) / 6250000000000000000), LB := ((2007804289421919 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((4994299113 : Rat) / 2048000000), D0 := ((4994299113 : Rat) / 2048000000), D1 := ((6360550541 : Rat) / 10240000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((85071833069196429 : Rat) / 400000000000000000), D4 := ((4303064671805244287 : Rat) / 12500000000000000000), LB := ((436649908675691 : Rat) / 625000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4994299113 : Rat) / 2048000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((244351767 : Rat) / 2048000000), D3 := ((84782590920758929 : Rat) / 400000000000000000), D4 := ((1073506463666643103 : Rat) / 3125000000000000000), LB := ((1498651739484727 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((24986304763 : Rat) / 10240000000), D0 := ((24986304763 : Rat) / 10240000000), D1 := ((6375359739 : Rat) / 10240000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((84493348772321429 : Rat) / 400000000000000000), D4 := ((4284987037527900537 : Rat) / 12500000000000000000), LB := ((1011232262391193 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24986304763 : Rat) / 10240000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((1206949637 : Rat) / 10240000000), D3 := ((84204106623883929 : Rat) / 400000000000000000), D4 := ((2137974110194614331 : Rat) / 6250000000000000000), LB := ((41713855038930103 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((25001113961 : Rat) / 10240000000), D0 := ((25001113961 : Rat) / 10240000000), D1 := ((6390168937 : Rat) / 10240000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((83914864475446429 : Rat) / 400000000000000000), D4 := ((4266909403250556787 : Rat) / 12500000000000000000), LB := ((3340608545795709 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25001113961 : Rat) / 10240000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((1192140439 : Rat) / 10240000000), D3 := ((83625622327008929 : Rat) / 400000000000000000), D4 := ((266116911631992807 : Rat) / 781250000000000000), LB := ((64104116610543 : Rat) / 250000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((156303241 : Rat) / 64000000), R := ((25015923159 : Rat) / 10240000000), D0 := ((25015923159 : Rat) / 10240000000), D1 := ((1280995627 : Rat) / 2048000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((83336380178571429 : Rat) / 400000000000000000), D4 := ((4248831768973213037 : Rat) / 12500000000000000000), LB := ((460598352499883 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25015923159 : Rat) / 10240000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((1177331241 : Rat) / 10240000000), D3 := ((83047138030133929 : Rat) / 400000000000000000), D4 := ((2119896475917270581 : Rat) / 6250000000000000000), LB := ((5878198840343629 : Rat) / 50000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((25030732357 : Rat) / 10240000000), D0 := ((25030732357 : Rat) / 10240000000), D1 := ((6419787333 : Rat) / 10240000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((82757895881696429 : Rat) / 400000000000000000), D4 := ((4230754134695869287 : Rat) / 12500000000000000000), LB := ((5642542745762369 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25030732357 : Rat) / 10240000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((1162522043 : Rat) / 10240000000), D3 := ((82468653733258929 : Rat) / 400000000000000000), D4 := ((1055428829389299353 : Rat) / 3125000000000000000), LB := ((4296567155948061 : Rat) / 5000000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((50083678511 : Rat) / 20480000000), D0 := ((50083678511 : Rat) / 20480000000), D1 := ((12861788463 : Rat) / 20480000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((82179411584821429 : Rat) / 400000000000000000), D4 := ((4212676500418525537 : Rat) / 12500000000000000000), LB := ((5639322959147819 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50083678511 : Rat) / 20480000000), R := ((5009108311 : Rat) / 2048000000), D0 := ((5009108311 : Rat) / 2048000000), D1 := ((6434596531 : Rat) / 10240000000), D2 := ((2302830289 : Rat) / 20480000000), D3 := ((82034790510602679 : Rat) / 400000000000000000), D4 := ((8416314183698379199 : Rat) / 25000000000000000000), LB := ((5407788314518713 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5009108311 : Rat) / 2048000000), R := ((50098487709 : Rat) / 20480000000), D0 := ((50098487709 : Rat) / 20480000000), D1 := ((12876597661 : Rat) / 20480000000), D2 := ((229542569 : Rat) / 2048000000), D3 := ((81890169436383929 : Rat) / 400000000000000000), D4 := ((2101818841639926831 : Rat) / 6250000000000000000), LB := ((1297604208592637 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50098487709 : Rat) / 20480000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((2288021091 : Rat) / 20480000000), D3 := ((81745548362165179 : Rat) / 400000000000000000), D4 := ((8398236549421035449 : Rat) / 25000000000000000000), LB := ((4987255447953531 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((50113296907 : Rat) / 20480000000), D0 := ((50113296907 : Rat) / 20480000000), D1 := ((12891406859 : Rat) / 20480000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((81600927287946429 : Rat) / 400000000000000000), D4 := ((4194598866141181787 : Rat) / 12500000000000000000), LB := ((959670294128967 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50113296907 : Rat) / 20480000000), R := ((25060350753 : Rat) / 10240000000), D0 := ((25060350753 : Rat) / 10240000000), D1 := ((6449405729 : Rat) / 10240000000), D2 := ((2273211893 : Rat) / 20480000000), D3 := ((81456306213727679 : Rat) / 400000000000000000), D4 := ((8380158915143691699 : Rat) / 25000000000000000000), LB := ((46237526082387737 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25060350753 : Rat) / 10240000000), R := ((10025621221 : Rat) / 4096000000), D0 := ((10025621221 : Rat) / 4096000000), D1 := ((12906216057 : Rat) / 20480000000), D2 := ((1132903647 : Rat) / 10240000000), D3 := ((81311685139508929 : Rat) / 400000000000000000), D4 := ((523195006125313739 : Rat) / 1562500000000000000), LB := ((2231753480605031 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10025621221 : Rat) / 4096000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 4096000000), D3 := ((81167064065290179 : Rat) / 400000000000000000), D4 := ((8362081280866347949 : Rat) / 25000000000000000000), LB := ((1079415757283611 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((50142915303 : Rat) / 20480000000), D0 := ((50142915303 : Rat) / 20480000000), D1 := ((2584205051 : Rat) / 4096000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((81022442991071429 : Rat) / 400000000000000000), D4 := ((4176521231863838037 : Rat) / 12500000000000000000), LB := ((418626971513153 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50142915303 : Rat) / 20480000000), R := ((25075159951 : Rat) / 10240000000), D0 := ((25075159951 : Rat) / 10240000000), D1 := ((6464214927 : Rat) / 10240000000), D2 := ((2243593497 : Rat) / 20480000000), D3 := ((80877821916852679 : Rat) / 400000000000000000), D4 := ((8344003646589004199 : Rat) / 25000000000000000000), LB := ((2034688165170051 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25075159951 : Rat) / 10240000000), R := ((50157724501 : Rat) / 20480000000), D0 := ((50157724501 : Rat) / 20480000000), D1 := ((12935834453 : Rat) / 20480000000), D2 := ((1118094449 : Rat) / 10240000000), D3 := ((80733200842633929 : Rat) / 400000000000000000), D4 := ((2083741207362583081 : Rat) / 6250000000000000000), LB := ((2479395374100149 : Rat) / 6250000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50157724501 : Rat) / 20480000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((2228784299 : Rat) / 20480000000), D3 := ((80588579768415179 : Rat) / 400000000000000000), D4 := ((8325926012311660449 : Rat) / 25000000000000000000), LB := ((1551715464342851 : Rat) / 4000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((501651291 : Rat) / 204800000), R := ((50172533699 : Rat) / 20480000000), D0 := ((50172533699 : Rat) / 20480000000), D1 := ((12950643651 : Rat) / 20480000000), D2 := ((22213797 : Rat) / 204800000), D3 := ((80443958694196429 : Rat) / 400000000000000000), D4 := ((4158443597586494287 : Rat) / 12500000000000000000), LB := ((152247803212191 : Rat) / 400000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50172533699 : Rat) / 20480000000), R := ((25089969149 : Rat) / 10240000000), D0 := ((25089969149 : Rat) / 10240000000), D1 := ((51832193 : Rat) / 81920000), D2 := ((2213975101 : Rat) / 20480000000), D3 := ((80299337619977679 : Rat) / 400000000000000000), D4 := ((8307848378034316699 : Rat) / 25000000000000000000), LB := ((4684753558505117 : Rat) / 12500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25089969149 : Rat) / 10240000000), R := ((50187342897 : Rat) / 20480000000), D0 := ((50187342897 : Rat) / 20480000000), D1 := ((12965452849 : Rat) / 20480000000), D2 := ((1103285251 : Rat) / 10240000000), D3 := ((80154716545758929 : Rat) / 400000000000000000), D4 := ((1037351195111955603 : Rat) / 3125000000000000000), LB := ((37041633819001607 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50187342897 : Rat) / 20480000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((2199165903 : Rat) / 20480000000), D3 := ((80010095471540179 : Rat) / 400000000000000000), D4 := ((8289770743756972949 : Rat) / 25000000000000000000), LB := ((3675328543794043 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((10040430419 : Rat) / 4096000000), D0 := ((10040430419 : Rat) / 4096000000), D1 := ((12980262047 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((79865474397321429 : Rat) / 400000000000000000), D4 := ((4140365963309150537 : Rat) / 12500000000000000000), LB := ((3661350632305771 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10040430419 : Rat) / 4096000000), R := ((25104778347 : Rat) / 10240000000), D0 := ((25104778347 : Rat) / 10240000000), D1 := ((6493833323 : Rat) / 10240000000), D2 := ((436871341 : Rat) / 4096000000), D3 := ((79720853323102679 : Rat) / 400000000000000000), D4 := ((8271693109479629199 : Rat) / 25000000000000000000), LB := ((1831141197015801 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25104778347 : Rat) / 10240000000), R := ((50216961293 : Rat) / 20480000000), D0 := ((50216961293 : Rat) / 20480000000), D1 := ((2599014249 : Rat) / 4096000000), D2 := ((1088476053 : Rat) / 10240000000), D3 := ((79576232248883929 : Rat) / 400000000000000000), D4 := ((2065663573085239331 : Rat) / 6250000000000000000), LB := ((7356354054960379 : Rat) / 20000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50216961293 : Rat) / 20480000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((2169547507 : Rat) / 20480000000), D3 := ((79431611174665179 : Rat) / 400000000000000000), D4 := ((8253615475202285449 : Rat) / 25000000000000000000), LB := ((7418176376717267 : Rat) / 20000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((50231770491 : Rat) / 20480000000), D0 := ((50231770491 : Rat) / 20480000000), D1 := ((13009880443 : Rat) / 20480000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((79286990100446429 : Rat) / 400000000000000000), D4 := ((4122288329031806787 : Rat) / 12500000000000000000), LB := ((1877534997459379 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50231770491 : Rat) / 20480000000), R := ((5023917509 : Rat) / 2048000000), D0 := ((5023917509 : Rat) / 2048000000), D1 := ((6508642521 : Rat) / 10240000000), D2 := ((2154738309 : Rat) / 20480000000), D3 := ((79142369026227679 : Rat) / 400000000000000000), D4 := ((8235537840924941699 : Rat) / 25000000000000000000), LB := ((38161770333977607 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5023917509 : Rat) / 2048000000), R := ((50246579689 : Rat) / 20480000000), D0 := ((50246579689 : Rat) / 20480000000), D1 := ((13024689641 : Rat) / 20480000000), D2 := ((214733371 : Rat) / 2048000000), D3 := ((78997747952008929 : Rat) / 400000000000000000), D4 := ((64269523623330233 : Rat) / 195312500000000000), LB := ((3892464363514647 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50246579689 : Rat) / 20480000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((2139929111 : Rat) / 20480000000), D3 := ((78853126877790179 : Rat) / 400000000000000000), D4 := ((8217460206647597949 : Rat) / 25000000000000000000), LB := ((248999220255567 : Rat) / 625000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((50261388887 : Rat) / 20480000000), D0 := ((50261388887 : Rat) / 20480000000), D1 := ((13039498839 : Rat) / 20480000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((78708505803571429 : Rat) / 400000000000000000), D4 := ((4104210694754463037 : Rat) / 12500000000000000000), LB := ((4090802538746219 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50261388887 : Rat) / 20480000000), R := ((25134396743 : Rat) / 10240000000), D0 := ((25134396743 : Rat) / 10240000000), D1 := ((6523451719 : Rat) / 10240000000), D2 := ((2125119913 : Rat) / 20480000000), D3 := ((78563884729352679 : Rat) / 400000000000000000), D4 := ((8199382572370254199 : Rat) / 25000000000000000000), LB := ((4212965921681633 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25134396743 : Rat) / 10240000000), R := ((10055239617 : Rat) / 4096000000), D0 := ((10055239617 : Rat) / 4096000000), D1 := ((13054308037 : Rat) / 20480000000), D2 := ((1058857657 : Rat) / 10240000000), D3 := ((78419263655133929 : Rat) / 400000000000000000), D4 := ((2047585938807895581 : Rat) / 6250000000000000000), LB := ((8701069367141323 : Rat) / 20000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10055239617 : Rat) / 4096000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((422062143 : Rat) / 4096000000), D3 := ((78274642580915179 : Rat) / 400000000000000000), D4 := ((8181304938092910449 : Rat) / 25000000000000000000), LB := ((4503566337532017 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((50291007283 : Rat) / 20480000000), D0 := ((50291007283 : Rat) / 20480000000), D1 := ((2613823447 : Rat) / 4096000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((78130021506696429 : Rat) / 400000000000000000), D4 := ((4086133060477119287 : Rat) / 12500000000000000000), LB := ((4672118905198197 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50291007283 : Rat) / 20480000000), R := ((25149205941 : Rat) / 10240000000), D0 := ((25149205941 : Rat) / 10240000000), D1 := ((6538260917 : Rat) / 10240000000), D2 := ((2095501517 : Rat) / 20480000000), D3 := ((77985400432477679 : Rat) / 400000000000000000), D4 := ((8163227303815566699 : Rat) / 25000000000000000000), LB := ((9712501845809407 : Rat) / 20000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25149205941 : Rat) / 10240000000), R := ((50305816481 : Rat) / 20480000000), D0 := ((50305816481 : Rat) / 20480000000), D1 := ((13083926433 : Rat) / 20480000000), D2 := ((1044048459 : Rat) / 10240000000), D3 := ((77840779358258929 : Rat) / 400000000000000000), D4 := ((1019273560834611853 : Rat) / 3125000000000000000), LB := ((5056021447949477 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50305816481 : Rat) / 20480000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((2080692319 : Rat) / 20480000000), D3 := ((77696158284040179 : Rat) / 400000000000000000), D4 := ((8145149669538222949 : Rat) / 25000000000000000000), LB := ((1054298012997501 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((50320625679 : Rat) / 20480000000), D0 := ((50320625679 : Rat) / 20480000000), D1 := ((13098735631 : Rat) / 20480000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((77551537209821429 : Rat) / 400000000000000000), D4 := ((4068055426199775537 : Rat) / 12500000000000000000), LB := ((1100543378499741 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50320625679 : Rat) / 20480000000), R := ((25164015139 : Rat) / 10240000000), D0 := ((25164015139 : Rat) / 10240000000), D1 := ((1310614023 : Rat) / 2048000000), D2 := ((2065883121 : Rat) / 20480000000), D3 := ((77406916135602679 : Rat) / 400000000000000000), D4 := ((8127072035260879199 : Rat) / 25000000000000000000), LB := ((1437440647351143 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25164015139 : Rat) / 10240000000), R := ((50335434877 : Rat) / 20480000000), D0 := ((50335434877 : Rat) / 20480000000), D1 := ((13113544829 : Rat) / 20480000000), D2 := ((1029239261 : Rat) / 10240000000), D3 := ((77262295061383929 : Rat) / 400000000000000000), D4 := ((2029508304530551831 : Rat) / 6250000000000000000), LB := ((6012688361742569 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50335434877 : Rat) / 20480000000), R := ((12585709869 : Rat) / 5120000000), D0 := ((12585709869 : Rat) / 5120000000), D1 := ((3280237357 : Rat) / 5120000000), D2 := ((2051073923 : Rat) / 20480000000), D3 := ((77117673987165179 : Rat) / 400000000000000000), D4 := ((8108994400983535449 : Rat) / 25000000000000000000), LB := ((3145777984752407 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12585709869 : Rat) / 5120000000), R := ((25178824337 : Rat) / 10240000000), D0 := ((25178824337 : Rat) / 10240000000), D1 := ((6567879313 : Rat) / 10240000000), D2 := ((510917331 : Rat) / 5120000000), D3 := ((76973052912946429 : Rat) / 400000000000000000), D4 := ((4049977791922431787 : Rat) / 12500000000000000000), LB := ((27918938679316607 : Rat) / 500000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25178824337 : Rat) / 10240000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((1014430063 : Rat) / 10240000000), D3 := ((76683810764508929 : Rat) / 400000000000000000), D4 := ((505117371847969989 : Rat) / 1562500000000000000), LB := ((12019530627727093 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((5038726707 : Rat) / 2048000000), D0 := ((5038726707 : Rat) / 2048000000), D1 := ((6582688511 : Rat) / 10240000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((76394568616071429 : Rat) / 400000000000000000), D4 := ((4031900157645088037 : Rat) / 12500000000000000000), LB := ((3820588711095363 : Rat) / 20000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5038726707 : Rat) / 2048000000), R := ((12600519067 : Rat) / 5120000000), D0 := ((12600519067 : Rat) / 5120000000), D1 := ((659009311 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 2048000000), D3 := ((76105326467633929 : Rat) / 400000000000000000), D4 := ((2011430670253208081 : Rat) / 6250000000000000000), LB := ((2683922183984999 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12600519067 : Rat) / 5120000000), R := ((25208442733 : Rat) / 10240000000), D0 := ((25208442733 : Rat) / 10240000000), D1 := ((6597497709 : Rat) / 10240000000), D2 := ((496108133 : Rat) / 5120000000), D3 := ((75816084319196429 : Rat) / 400000000000000000), D4 := ((4013822523367744287 : Rat) / 12500000000000000000), LB := ((35233657610922453 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25208442733 : Rat) / 10240000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((984811667 : Rat) / 10240000000), D3 := ((75526842170758929 : Rat) / 400000000000000000), D4 := ((1001195926557268103 : Rat) / 3125000000000000000), LB := ((44291642327015657 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((25223251931 : Rat) / 10240000000), D0 := ((25223251931 : Rat) / 10240000000), D1 := ((6612306907 : Rat) / 10240000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((75237600022321429 : Rat) / 400000000000000000), D4 := ((3995744889090400537 : Rat) / 12500000000000000000), LB := ((5401866938294919 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25223251931 : Rat) / 10240000000), R := ((2523065653 : Rat) / 1024000000), D0 := ((2523065653 : Rat) / 1024000000), D1 := ((3309855753 : Rat) / 5120000000), D2 := ((970002469 : Rat) / 10240000000), D3 := ((74948357873883929 : Rat) / 400000000000000000), D4 := ((1993353035975864331 : Rat) / 6250000000000000000), LB := ((6442033681045289 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2523065653 : Rat) / 1024000000), R := ((25238061129 : Rat) / 10240000000), D0 := ((25238061129 : Rat) / 10240000000), D1 := ((1325423221 : Rat) / 2048000000), D2 := ((96259787 : Rat) / 1024000000), D3 := ((74659115725446429 : Rat) / 400000000000000000), D4 := ((3977667254813056787 : Rat) / 12500000000000000000), LB := ((7550235007579009 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25238061129 : Rat) / 10240000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((955193271 : Rat) / 10240000000), D3 := ((74369873577008929 : Rat) / 400000000000000000), D4 := ((248039277354649057 : Rat) / 781250000000000000), LB := ((1745410499553679 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((197230201 : Rat) / 80000000), R := ((25252870327 : Rat) / 10240000000), D0 := ((25252870327 : Rat) / 10240000000), D1 := ((6641925303 : Rat) / 10240000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((74080631428571429 : Rat) / 400000000000000000), D4 := ((3959589620535713037 : Rat) / 12500000000000000000), LB := ((9973079065180301 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25252870327 : Rat) / 10240000000), R := ((12630137463 : Rat) / 5120000000), D0 := ((12630137463 : Rat) / 5120000000), D1 := ((3324664951 : Rat) / 5120000000), D2 := ((940384073 : Rat) / 10240000000), D3 := ((73791389280133929 : Rat) / 400000000000000000), D4 := ((1975275401698520581 : Rat) / 6250000000000000000), LB := ((2822229817128763 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12630137463 : Rat) / 5120000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((466489737 : Rat) / 5120000000), D3 := ((73502147131696429 : Rat) / 400000000000000000), D4 := ((3941511986258369287 : Rat) / 12500000000000000000), LB := ((7592800977904157 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((12644946661 : Rat) / 5120000000), D0 := ((12644946661 : Rat) / 5120000000), D1 := ((3339474149 : Rat) / 5120000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((72923662834821429 : Rat) / 400000000000000000), D4 := ((3923434351981025537 : Rat) / 12500000000000000000), LB := ((941822673708459 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12644946661 : Rat) / 5120000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 5120000000), D3 := ((72345178537946429 : Rat) / 400000000000000000), D4 := ((3905356717703681787 : Rat) / 12500000000000000000), LB := ((7064644277252063 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((632617563 : Rat) / 256000000), R := ((12659755859 : Rat) / 5120000000), D0 := ((12659755859 : Rat) / 5120000000), D1 := ((3354283347 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((71766694241071429 : Rat) / 400000000000000000), D4 := ((3887279083426338037 : Rat) / 12500000000000000000), LB := ((10656740368207573 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12659755859 : Rat) / 5120000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((436871341 : Rat) / 5120000000), D3 := ((71188209944196429 : Rat) / 400000000000000000), D4 := ((3869201449148994287 : Rat) / 12500000000000000000), LB := ((14549205504950091 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((12674565057 : Rat) / 5120000000), D0 := ((12674565057 : Rat) / 5120000000), D1 := ((673818509 : Rat) / 1024000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((70609725647321429 : Rat) / 400000000000000000), D4 := ((3851123814871650537 : Rat) / 12500000000000000000), LB := ((1874790697889761 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12674565057 : Rat) / 5120000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((422062143 : Rat) / 5120000000), D3 := ((70031241350446429 : Rat) / 400000000000000000), D4 := ((3833046180594306787 : Rat) / 12500000000000000000), LB := ((11629483852206163 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((69452757053571429 : Rat) / 400000000000000000), D4 := ((3814968546316963037 : Rat) / 12500000000000000000), LB := ((1146972729239859 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((68295788459821429 : Rat) / 400000000000000000), D4 := ((3778813277762275537 : Rat) / 12500000000000000000), LB := ((3062904378791087 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((67138819866071429 : Rat) / 400000000000000000), D4 := ((3742658009207588037 : Rat) / 12500000000000000000), LB := ((2739982593921747 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((65981851272321429 : Rat) / 400000000000000000), D4 := ((3706502740652900537 : Rat) / 12500000000000000000), LB := ((255667181531527 : Rat) / 62500000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((64824882678571429 : Rat) / 400000000000000000), D4 := ((3670347472098213037 : Rat) / 12500000000000000000), LB := ((9685987237506577 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((62510945491071429 : Rat) / 400000000000000000), D4 := ((3598036934988838037 : Rat) / 12500000000000000000), LB := ((8958422994481019 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((60197008303571429 : Rat) / 400000000000000000), D4 := ((3525726397879463037 : Rat) / 12500000000000000000), LB := ((543138851866503 : Rat) / 62500000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((57883071116071429 : Rat) / 400000000000000000), D4 := ((3453415860770088037 : Rat) / 12500000000000000000), LB := ((13694093474847291 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((55569133928571429 : Rat) / 400000000000000000), D4 := ((3381105323660713037 : Rat) / 12500000000000000000), LB := ((10663660862491903 : Rat) / 1000000000000000000) }
]

def block389RightChunk000L : Rat := ((8706167410714285731 : Rat) / 5000000000000000000)
def block389RightChunk000R : Rat := ((1614864603 : Rat) / 640000000)

def block389RightChunk000Certificate : Bool :=
  allBoxesValid block389RightChunk000 &&
  coversFromBool block389RightChunk000 block389RightChunk000L block389RightChunk000R

theorem block389RightChunk000Certificate_eq_true :
    block389RightChunk000Certificate = true := by
  native_decide

def block389RightChunk001 : List RatBox := [
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((50941259553571429 : Rat) / 400000000000000000), D4 := ((3236484249441963037 : Rat) / 12500000000000000000), LB := ((26076783664824937 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((46313385178571429 : Rat) / 400000000000000000), D4 := ((3091863175223213037 : Rat) / 12500000000000000000), LB := ((31050872127128787 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((511587 : Rat) / 200000), R := ((4129753636428571429 : Rat) / 1600000000000000000), D0 := ((4129753636428571429 : Rat) / 1600000000000000000), D1 := ((1221793476428571429 : Rat) / 1600000000000000000), D2 := ((37057636428571429 : Rat) / 1600000000000000000), D3 := ((37057636428571429 : Rat) / 400000000000000000), D4 := ((2802621026785713037 : Rat) / 12500000000000000000), LB := ((988304848159069 : Rat) / 20000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4129753636428571429 : Rat) / 1600000000000000000), R := ((2083405636428571429 : Rat) / 800000000000000000), D0 := ((2083405636428571429 : Rat) / 800000000000000000), D1 := ((629425556428571429 : Rat) / 800000000000000000), D2 := ((37057636428571429 : Rat) / 800000000000000000), D3 := ((111172909285714287 : Rat) / 1600000000000000000), D4 := ((40209731874999979967 : Rat) / 200000000000000000000), LB := ((1049599763819557 : Rat) / 20000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2083405636428571429 : Rat) / 800000000000000000), R := ((1060231636428571429 : Rat) / 400000000000000000), D0 := ((1060231636428571429 : Rat) / 400000000000000000), D1 := ((333241596428571429 : Rat) / 400000000000000000), D2 := ((37057636428571429 : Rat) / 400000000000000000), D3 := ((37057636428571429 : Rat) / 800000000000000000), D4 := ((17788763660714275671 : Rat) / 100000000000000000000), LB := ((37421968228319 : Rat) / 800000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1060231636428571429 : Rat) / 400000000000000000), R := ((134800201607142857253 : Rat) / 50000000000000000000), D0 := ((134800201607142857253 : Rat) / 50000000000000000000), D1 := ((43926446607142857253 : Rat) / 50000000000000000000), D2 := ((6903451607142857253 : Rat) / 50000000000000000000), D3 := ((567811763392857157 : Rat) / 12500000000000000000), D4 := ((6578279553571423523 : Rat) / 50000000000000000000), LB := ((17622134706227033 : Rat) / 1000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((134800201607142857253 : Rat) / 50000000000000000000), R := ((13536801337053571441 : Rat) / 5000000000000000000), D0 := ((13536801337053571441 : Rat) / 5000000000000000000), D1 := ((4449425837053571441 : Rat) / 5000000000000000000), D2 := ((747126337053571441 : Rat) / 5000000000000000000), D3 := ((567811763392857157 : Rat) / 10000000000000000000), D4 := ((861406499999998979 : Rat) / 10000000000000000000), LB := ((1173857072333831 : Rat) / 50000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((13536801337053571441 : Rat) / 5000000000000000000), R := ((271303838504464285977 : Rat) / 100000000000000000000), D0 := ((271303838504464285977 : Rat) / 100000000000000000000), D1 := ((89556328504464285977 : Rat) / 100000000000000000000), D2 := ((15510338504464285977 : Rat) / 100000000000000000000), D3 := ((6245929397321428727 : Rat) / 100000000000000000000), D4 := ((1869610368303568869 : Rat) / 25000000000000000000), LB := ((190621795718387 : Rat) / 10000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((271303838504464285977 : Rat) / 100000000000000000000), R := ((135935825133928571567 : Rat) / 50000000000000000000), D0 := ((135935825133928571567 : Rat) / 50000000000000000000), D1 := ((45062070133928571567 : Rat) / 50000000000000000000), D2 := ((8039075133928571567 : Rat) / 50000000000000000000), D3 := ((1703435290178571471 : Rat) / 25000000000000000000), D4 := ((6910629709821418319 : Rat) / 100000000000000000000), LB := ((1763872390920851 : Rat) / 250000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((135935825133928571567 : Rat) / 50000000000000000000), R := ((21772444491964285737 : Rat) / 8000000000000000000), D0 := ((21772444491964285737 : Rat) / 8000000000000000000), D1 := ((7232643691964285737 : Rat) / 8000000000000000000), D2 := ((1308964491964285737 : Rat) / 8000000000000000000), D3 := ((567811763392857157 : Rat) / 8000000000000000000), D4 := ((3171408973214280581 : Rat) / 50000000000000000000), LB := ((4143186513786923 : Rat) / 500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((21772444491964285737 : Rat) / 8000000000000000000), R := ((272439462031250000291 : Rat) / 100000000000000000000), D0 := ((272439462031250000291 : Rat) / 100000000000000000000), D1 := ((90691952031250000291 : Rat) / 100000000000000000000), D2 := ((16645962031250000291 : Rat) / 100000000000000000000), D3 := ((7381552924107143041 : Rat) / 100000000000000000000), D4 := ((12117824129464265167 : Rat) / 200000000000000000000), LB := ((7976379159743141 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((272439462031250000291 : Rat) / 100000000000000000000), R := ((545446735825892857739 : Rat) / 200000000000000000000), D0 := ((545446735825892857739 : Rat) / 200000000000000000000), D1 := ((181951715825892857739 : Rat) / 200000000000000000000), D2 := ((33859735825892857739 : Rat) / 200000000000000000000), D3 := ((15330917611607143239 : Rat) / 200000000000000000000), D4 := ((1155001236607140801 : Rat) / 20000000000000000000), LB := ((56760591715177 : Rat) / 200000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((545446735825892857739 : Rat) / 200000000000000000000), R := ((218292256683035714527 : Rat) / 80000000000000000000), D0 := ((218292256683035714527 : Rat) / 80000000000000000000), D1 := ((72894248683035714527 : Rat) / 80000000000000000000), D2 := ((13657456683035714527 : Rat) / 80000000000000000000), D3 := ((6245929397321428727 : Rat) / 80000000000000000000), D4 := ((10982200602678550853 : Rat) / 200000000000000000000), LB := ((594798932482099 : Rat) / 250000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((218292256683035714527 : Rat) / 80000000000000000000), R := ((34125909224330357181 : Rat) / 12500000000000000000), D0 := ((34125909224330357181 : Rat) / 12500000000000000000), D1 := ((11407470474330357181 : Rat) / 12500000000000000000), D2 := ((2151721724330357181 : Rat) / 12500000000000000000), D3 := ((3974682343750000099 : Rat) / 50000000000000000000), D4 := ((21396589441964244549 : Rat) / 400000000000000000000), LB := ((5025741934208683 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((34125909224330357181 : Rat) / 12500000000000000000), R := ((2184626002120535716741 : Rat) / 800000000000000000000), D0 := ((2184626002120535716741 : Rat) / 800000000000000000000), D1 := ((730645922120535716741 : Rat) / 800000000000000000000), D2 := ((138278002120535716741 : Rat) / 800000000000000000000), D3 := ((64162729263392858741 : Rat) / 800000000000000000000), D4 := ((40681206403459741 : Rat) / 781250000000000000), LB := ((23524381653602933 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2184626002120535716741 : Rat) / 800000000000000000000), R := ((1092596906941964286949 : Rat) / 400000000000000000000), D0 := ((1092596906941964286949 : Rat) / 400000000000000000000), D1 := ((365606866941964286949 : Rat) / 400000000000000000000), D2 := ((69422906941964286949 : Rat) / 400000000000000000000), D3 := ((32365270513392857949 : Rat) / 400000000000000000000), D4 := ((41089743593749917627 : Rat) / 800000000000000000000), LB := ((358807380153503 : Rat) / 200000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1092596906941964286949 : Rat) / 400000000000000000000), R := ((437152325129464286211 : Rat) / 160000000000000000000), D0 := ((437152325129464286211 : Rat) / 160000000000000000000), D1 := ((146356309129464286211 : Rat) / 160000000000000000000), D2 := ((27882725129464286211 : Rat) / 160000000000000000000), D3 := ((13059670558035714611 : Rat) / 160000000000000000000), D4 := ((4052193183035706047 : Rat) / 80000000000000000000), LB := ((6389198581973343 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((437152325129464286211 : Rat) / 160000000000000000000), R := ((546582359352678572053 : Rat) / 200000000000000000000), D0 := ((546582359352678572053 : Rat) / 200000000000000000000), D1 := ((183087339352678572053 : Rat) / 200000000000000000000), D2 := ((34995359352678572053 : Rat) / 200000000000000000000), D3 := ((16466541138392857553 : Rat) / 200000000000000000000), D4 := ((39954120066964203313 : Rat) / 800000000000000000000), LB := ((8043989416276487 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((546582359352678572053 : Rat) / 200000000000000000000), R := ((2186897249174107145369 : Rat) / 800000000000000000000), D0 := ((2186897249174107145369 : Rat) / 800000000000000000000), D1 := ((732917169174107145369 : Rat) / 800000000000000000000), D2 := ((140549249174107145369 : Rat) / 800000000000000000000), D3 := ((66433976316964287369 : Rat) / 800000000000000000000), D4 := ((9846577075892836539 : Rat) / 200000000000000000000), LB := ((3743065689401637 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2186897249174107145369 : Rat) / 800000000000000000000), R := ((874872462022321429579 : Rat) / 320000000000000000000), D0 := ((874872462022321429579 : Rat) / 320000000000000000000), D1 := ((293280430022321429579 : Rat) / 320000000000000000000), D2 := ((56333262022321429579 : Rat) / 320000000000000000000), D3 := ((26687152879464286379 : Rat) / 320000000000000000000), D4 := ((38818496540178488999 : Rat) / 800000000000000000000), LB := ((12380829962700957 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((874872462022321429579 : Rat) / 320000000000000000000), R := ((1093732530468750001263 : Rat) / 400000000000000000000), D0 := ((1093732530468750001263 : Rat) / 400000000000000000000), D1 := ((366742490468750001263 : Rat) / 400000000000000000000), D2 := ((70558530468750001263 : Rat) / 400000000000000000000), D3 := ((33500894040178572263 : Rat) / 400000000000000000000), D4 := ((77069181316964120841 : Rat) / 1600000000000000000000), LB := ((5291825626058677 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1093732530468750001263 : Rat) / 400000000000000000000), R := ((4375497933638392862209 : Rat) / 1600000000000000000000), D0 := ((4375497933638392862209 : Rat) / 1600000000000000000000), D1 := ((1467537773638392862209 : Rat) / 1600000000000000000000), D2 := ((282801933638392862209 : Rat) / 1600000000000000000000), D3 := ((134571387924107146209 : Rat) / 1600000000000000000000), D4 := ((19125342388392815921 : Rat) / 400000000000000000000), LB := ((8899265243799137 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4375497933638392862209 : Rat) / 1600000000000000000000), R := ((2188032872700892859683 : Rat) / 800000000000000000000), D0 := ((2188032872700892859683 : Rat) / 800000000000000000000), D1 := ((734052792700892859683 : Rat) / 800000000000000000000), D2 := ((141684872700892859683 : Rat) / 800000000000000000000), D3 := ((67569599843750001683 : Rat) / 800000000000000000000), D4 := ((75933557790178406527 : Rat) / 1600000000000000000000), LB := ((7328585717079061 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2188032872700892859683 : Rat) / 800000000000000000000), R := ((4376633557165178576523 : Rat) / 1600000000000000000000), D0 := ((4376633557165178576523 : Rat) / 1600000000000000000000), D1 := ((1468673397165178576523 : Rat) / 1600000000000000000000), D2 := ((283937557165178576523 : Rat) / 1600000000000000000000), D3 := ((135707011450892860523 : Rat) / 1600000000000000000000), D4 := ((7536574602678554937 : Rat) / 160000000000000000000), LB := ((2936278142821047 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4376633557165178576523 : Rat) / 1600000000000000000000), R := ((54715017111607142921 : Rat) / 20000000000000000000), D0 := ((54715017111607142921 : Rat) / 20000000000000000000), D1 := ((18365515111607142921 : Rat) / 20000000000000000000), D2 := ((3556317111607142921 : Rat) / 20000000000000000000), D3 := ((1703435290178571471 : Rat) / 20000000000000000000), D4 := ((74797934263392692213 : Rat) / 1600000000000000000000), LB := ((4532151146311447 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((54715017111607142921 : Rat) / 20000000000000000000), R := ((4377769180691964290837 : Rat) / 1600000000000000000000), D0 := ((4377769180691964290837 : Rat) / 1600000000000000000000), D1 := ((1469809020691964290837 : Rat) / 1600000000000000000000), D2 := ((285073180691964290837 : Rat) / 1600000000000000000000), D3 := ((136842634977678574837 : Rat) / 1600000000000000000000), D4 := ((4639382656249989691 : Rat) / 100000000000000000000), LB := ((1654187929757689 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4377769180691964290837 : Rat) / 1600000000000000000000), R := ((2189168496227678573997 : Rat) / 800000000000000000000), D0 := ((2189168496227678573997 : Rat) / 800000000000000000000), D1 := ((735188416227678573997 : Rat) / 800000000000000000000), D2 := ((142820496227678573997 : Rat) / 800000000000000000000), D3 := ((68705223370535715997 : Rat) / 800000000000000000000), D4 := ((73662310736606977899 : Rat) / 1600000000000000000000), LB := ((1376417601869559 : Rat) / 6250000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2189168496227678573997 : Rat) / 800000000000000000000), R := ((4378904804218750005151 : Rat) / 1600000000000000000000), D0 := ((4378904804218750005151 : Rat) / 1600000000000000000000), D1 := ((1470944644218750005151 : Rat) / 1600000000000000000000), D2 := ((286208804218750005151 : Rat) / 1600000000000000000000), D3 := ((137978258504464289151 : Rat) / 1600000000000000000000), D4 := ((36547249486607060371 : Rat) / 800000000000000000000), LB := ((6074494099131411 : Rat) / 50000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4378904804218750005151 : Rat) / 1600000000000000000000), R := ((1094868153995535715577 : Rat) / 400000000000000000000), D0 := ((1094868153995535715577 : Rat) / 400000000000000000000), D1 := ((367878113995535715577 : Rat) / 400000000000000000000), D2 := ((71694153995535715577 : Rat) / 400000000000000000000), D3 := ((34636517566964286577 : Rat) / 400000000000000000000), D4 := ((14505337441964252717 : Rat) / 320000000000000000000), LB := ((3473725029135011 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1094868153995535715577 : Rat) / 400000000000000000000), R := ((8759513043727678581773 : Rat) / 3200000000000000000000), D0 := ((8759513043727678581773 : Rat) / 3200000000000000000000), D1 := ((2943592723727678581773 : Rat) / 3200000000000000000000), D2 := ((574121043727678581773 : Rat) / 3200000000000000000000), D3 := ((277659952299107149773 : Rat) / 3200000000000000000000), D4 := ((17989718861607101607 : Rat) / 400000000000000000000), LB := ((1139904043630957 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8759513043727678581773 : Rat) / 3200000000000000000000), R := ((876008085549107143893 : Rat) / 320000000000000000000), D0 := ((876008085549107143893 : Rat) / 320000000000000000000), D1 := ((294416053549107143893 : Rat) / 320000000000000000000), D2 := ((57468885549107143893 : Rat) / 320000000000000000000), D3 := ((27822776406250000693 : Rat) / 320000000000000000000), D4 := ((143349939129463955699 : Rat) / 3200000000000000000000), LB := ((1072827508692531 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((876008085549107143893 : Rat) / 320000000000000000000), R := ((8760648667254464296087 : Rat) / 3200000000000000000000), D0 := ((8760648667254464296087 : Rat) / 3200000000000000000000), D1 := ((2944728347254464296087 : Rat) / 3200000000000000000000), D2 := ((575256667254464296087 : Rat) / 3200000000000000000000), D3 := ((278795575825892864087 : Rat) / 3200000000000000000000), D4 := ((71391063683035549271 : Rat) / 1600000000000000000000), LB := ((1011894777940503 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8760648667254464296087 : Rat) / 3200000000000000000000), R := ((2190304119754464288311 : Rat) / 800000000000000000000), D0 := ((2190304119754464288311 : Rat) / 800000000000000000000), D1 := ((736324039754464288311 : Rat) / 800000000000000000000), D2 := ((143956119754464288311 : Rat) / 800000000000000000000), D3 := ((69840846897321430311 : Rat) / 800000000000000000000), D4 := ((28442863120535648277 : Rat) / 640000000000000000000), LB := ((299105109249527 : Rat) / 625000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2190304119754464288311 : Rat) / 800000000000000000000), R := ((8761784290781250010401 : Rat) / 3200000000000000000000), D0 := ((8761784290781250010401 : Rat) / 3200000000000000000000), D1 := ((2945863970781250010401 : Rat) / 3200000000000000000000), D2 := ((576392290781250010401 : Rat) / 3200000000000000000000), D3 := ((279931199352678578401 : Rat) / 3200000000000000000000), D4 := ((35411625959821346057 : Rat) / 800000000000000000000), LB := ((5678644969562413 : Rat) / 12500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8761784290781250010401 : Rat) / 3200000000000000000000), R := ((4381176051272321433779 : Rat) / 1600000000000000000000), D0 := ((4381176051272321433779 : Rat) / 1600000000000000000000), D1 := ((1473215891272321433779 : Rat) / 1600000000000000000000), D2 := ((288480051272321433779 : Rat) / 1600000000000000000000), D3 := ((140249505558035717779 : Rat) / 1600000000000000000000), D4 := ((141078692075892527071 : Rat) / 3200000000000000000000), LB := ((4331333829953321 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4381176051272321433779 : Rat) / 1600000000000000000000), R := ((1752583982861607144943 : Rat) / 640000000000000000000), D0 := ((1752583982861607144943 : Rat) / 640000000000000000000), D1 := ((589399918861607144943 : Rat) / 640000000000000000000), D2 := ((115505582861607144943 : Rat) / 640000000000000000000), D3 := ((56213364575892858543 : Rat) / 640000000000000000000), D4 := ((70255440156249834957 : Rat) / 1600000000000000000000), LB := ((41510950025197557 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1752583982861607144943 : Rat) / 640000000000000000000), R := ((547717982879464286367 : Rat) / 200000000000000000000), D0 := ((547717982879464286367 : Rat) / 200000000000000000000), D1 := ((184222962879464286367 : Rat) / 200000000000000000000), D2 := ((36130982879464286367 : Rat) / 200000000000000000000), D3 := ((17602164665178571867 : Rat) / 200000000000000000000), D4 := ((139943068549106812757 : Rat) / 3200000000000000000000), LB := ((2001180827252147 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((547717982879464286367 : Rat) / 200000000000000000000), R := ((8764055537834821439029 : Rat) / 3200000000000000000000), D0 := ((8764055537834821439029 : Rat) / 3200000000000000000000), D1 := ((2948135217834821439029 : Rat) / 3200000000000000000000), D2 := ((578663537834821439029 : Rat) / 3200000000000000000000), D3 := ((282202446406250007029 : Rat) / 3200000000000000000000), D4 := ((348438141964284889 : Rat) / 8000000000000000000), LB := ((3885298452637187 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8764055537834821439029 : Rat) / 3200000000000000000000), R := ((4382311674799107148093 : Rat) / 1600000000000000000000), D0 := ((4382311674799107148093 : Rat) / 1600000000000000000000), D1 := ((1474351514799107148093 : Rat) / 1600000000000000000000), D2 := ((289615674799107148093 : Rat) / 1600000000000000000000), D3 := ((141385129084821432093 : Rat) / 1600000000000000000000), D4 := ((138807445022321098443 : Rat) / 3200000000000000000000), LB := ((3800072605734117 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4382311674799107148093 : Rat) / 1600000000000000000000), R := ((8765191161361607153343 : Rat) / 3200000000000000000000), D0 := ((8765191161361607153343 : Rat) / 3200000000000000000000), D1 := ((2949270841361607153343 : Rat) / 3200000000000000000000), D2 := ((579799161361607153343 : Rat) / 3200000000000000000000), D3 := ((283338069933035721343 : Rat) / 3200000000000000000000), D4 := ((69119816629464120643 : Rat) / 1600000000000000000000), LB := ((3746853902419911 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8765191161361607153343 : Rat) / 3200000000000000000000), R := ((17531517946250000021 : Rat) / 6400000000000000000), D0 := ((17531517946250000021 : Rat) / 6400000000000000000), D1 := ((5899677306250000021 : Rat) / 6400000000000000000), D2 := ((1160733946250000021 : Rat) / 6400000000000000000), D3 := ((567811763392857157 : Rat) / 6400000000000000000), D4 := ((137671821495535384129 : Rat) / 3200000000000000000000), LB := ((931453687325473 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17531517946250000021 : Rat) / 6400000000000000000), R := ((8766326784888392867657 : Rat) / 3200000000000000000000), D0 := ((8766326784888392867657 : Rat) / 3200000000000000000000), D1 := ((2950406464888392867657 : Rat) / 3200000000000000000000), D2 := ((580934784888392867657 : Rat) / 3200000000000000000000), D3 := ((284473693459821435657 : Rat) / 3200000000000000000000), D4 := ((34276002433035631743 : Rat) / 800000000000000000000), LB := ((3737130210190731 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8766326784888392867657 : Rat) / 3200000000000000000000), R := ((4383447298325892862407 : Rat) / 1600000000000000000000), D0 := ((4383447298325892862407 : Rat) / 1600000000000000000000), D1 := ((1475487138325892862407 : Rat) / 1600000000000000000000), D2 := ((290751298325892862407 : Rat) / 1600000000000000000000), D3 := ((142520752611607146407 : Rat) / 1600000000000000000000), D4 := ((27307239593749933963 : Rat) / 640000000000000000000), LB := ((3780978046115657 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4383447298325892862407 : Rat) / 1600000000000000000000), R := ((8767462408415178581971 : Rat) / 3200000000000000000000), D0 := ((8767462408415178581971 : Rat) / 3200000000000000000000), D1 := ((2951542088415178581971 : Rat) / 3200000000000000000000), D2 := ((582070408415178581971 : Rat) / 3200000000000000000000), D3 := ((285609316986607149971 : Rat) / 3200000000000000000000), D4 := ((67984193102678406329 : Rat) / 1600000000000000000000), LB := ((3857538756183443 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8767462408415178581971 : Rat) / 3200000000000000000000), R := ((1096003777522321429891 : Rat) / 400000000000000000000), D0 := ((1096003777522321429891 : Rat) / 400000000000000000000), D1 := ((369013737522321429891 : Rat) / 400000000000000000000), D2 := ((72829777522321429891 : Rat) / 400000000000000000000), D3 := ((35772141093750000891 : Rat) / 400000000000000000000), D4 := ((135400574441963955501 : Rat) / 3200000000000000000000), LB := ((1983497809663337 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1096003777522321429891 : Rat) / 400000000000000000000), R := ((1753719606388392859257 : Rat) / 640000000000000000000), D0 := ((1753719606388392859257 : Rat) / 640000000000000000000), D1 := ((590535542388392859257 : Rat) / 640000000000000000000), D2 := ((116641206388392859257 : Rat) / 640000000000000000000), D3 := ((57348988102678572857 : Rat) / 640000000000000000000), D4 := ((16854095334821387293 : Rat) / 400000000000000000000), LB := ((41095347371111757 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1753719606388392859257 : Rat) / 640000000000000000000), R := ((4384582921852678576721 : Rat) / 1600000000000000000000), D0 := ((4384582921852678576721 : Rat) / 1600000000000000000000), D1 := ((1476622761852678576721 : Rat) / 1600000000000000000000), D2 := ((291886921852678576721 : Rat) / 1600000000000000000000), D3 := ((143656376138392860721 : Rat) / 1600000000000000000000), D4 := ((134264950915178241187 : Rat) / 3200000000000000000000), LB := ((1071336269306139 : Rat) / 2500000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4384582921852678576721 : Rat) / 1600000000000000000000), R := ((8769733655468750010599 : Rat) / 3200000000000000000000), D0 := ((8769733655468750010599 : Rat) / 3200000000000000000000), D1 := ((2953813335468750010599 : Rat) / 3200000000000000000000), D2 := ((584341655468750010599 : Rat) / 3200000000000000000000), D3 := ((287880564040178578599 : Rat) / 3200000000000000000000), D4 := ((13369713915178538403 : Rat) / 320000000000000000000), LB := ((44946185182298537 : Rat) / 100000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8769733655468750010599 : Rat) / 3200000000000000000000), R := ((2192575366808035716939 : Rat) / 800000000000000000000), D0 := ((2192575366808035716939 : Rat) / 800000000000000000000), D1 := ((738595286808035716939 : Rat) / 800000000000000000000), D2 := ((146227366808035716939 : Rat) / 800000000000000000000), D3 := ((72112093950892858939 : Rat) / 800000000000000000000), D4 := ((133129327388392526873 : Rat) / 3200000000000000000000), LB := ((4737549895036941 : Rat) / 10000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2192575366808035716939 : Rat) / 800000000000000000000), R := ((8770869278995535724913 : Rat) / 3200000000000000000000), D0 := ((8770869278995535724913 : Rat) / 3200000000000000000000), D1 := ((2954948958995535724913 : Rat) / 3200000000000000000000), D2 := ((585477278995535724913 : Rat) / 3200000000000000000000), D3 := ((289016187566964292913 : Rat) / 3200000000000000000000), D4 := ((33140378906249917429 : Rat) / 800000000000000000000), LB := ((2507168522790093 : Rat) / 5000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8770869278995535724913 : Rat) / 3200000000000000000000), R := ((877143709075892858207 : Rat) / 320000000000000000000), D0 := ((877143709075892858207 : Rat) / 320000000000000000000), D1 := ((295551677075892858207 : Rat) / 320000000000000000000), D2 := ((58604509075892858207 : Rat) / 320000000000000000000), D3 := ((28958399933035715007 : Rat) / 320000000000000000000), D4 := ((131993703861606812559 : Rat) / 3200000000000000000000), LB := ((1065036171679301 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((877143709075892858207 : Rat) / 320000000000000000000), R := ((8772004902522321439227 : Rat) / 3200000000000000000000), D0 := ((8772004902522321439227 : Rat) / 3200000000000000000000), D1 := ((2956084582522321439227 : Rat) / 3200000000000000000000), D2 := ((586612902522321439227 : Rat) / 3200000000000000000000), D3 := ((290151811093750007227 : Rat) / 3200000000000000000000), D4 := ((65712946049106977701 : Rat) / 1600000000000000000000), LB := ((1134057064283267 : Rat) / 2000000000000000000) },
  { w1 := ((8082794833719401 : Rat) / 10000000000000000), w2 := ((10376311987954391 : Rat) / 250000000000000000), w3 := ((3408093925587421 : Rat) / 20000000000000000), w4 := ((7289432713918531 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((1060231636428571429 : Rat) / 400000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8772004902522321439227 : Rat) / 3200000000000000000000), R := ((137071448660714285881 : Rat) / 50000000000000000000), D0 := ((137071448660714285881 : Rat) / 50000000000000000000), D1 := ((46197693660714285881 : Rat) / 50000000000000000000), D2 := ((9174698660714285881 : Rat) / 50000000000000000000), D3 := ((567811763392857157 : Rat) / 6250000000000000000), D4 := ((26171616066964219649 : Rat) / 640000000000000000000), LB := ((6049857571702177 : Rat) / 10000000000000000000) }
]

def block389RightChunk001L : Rat := ((1614864603 : Rat) / 640000000)
def block389RightChunk001R : Rat := ((137071448660714285881 : Rat) / 50000000000000000000)

def block389RightChunk001Certificate : Bool :=
  allBoxesValid block389RightChunk001 &&
  coversFromBool block389RightChunk001 block389RightChunk001L block389RightChunk001R

theorem block389RightChunk001Certificate_eq_true :
    block389RightChunk001Certificate = true := by
  native_decide

def block389RightChainCertificate : Bool :=
  decide (
    block389RightL = ((8706167410714285731 : Rat) / 5000000000000000000) /\
    ((1614864603 : Rat) / 640000000) = ((1614864603 : Rat) / 640000000) /\
    ((137071448660714285881 : Rat) / 50000000000000000000) = block389RightR)

theorem block389RightChainCertificate_eq_true :
    block389RightChainCertificate = true := by
  native_decide

def block389LeftBoxCount : Nat := boxCount block389LeftBoxes
def block389RightBoxCount : Nat := 153

def block389_rational_certificate : Prop :=
    block389LeftCertificate = true /\
    block389RightChainCertificate = true /\
    block389RightChunk000Certificate = true /\
    block389RightChunk001Certificate = true

theorem block389_rational_certificate_proof :
    block389_rational_certificate := by
  exact ⟨block389LeftCertificate_eq_true, block389RightChainCertificate_eq_true, block389RightChunk000Certificate_eq_true, block389RightChunk001Certificate_eq_true⟩

end Block389
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block389

open Set

def block389W1 : Rat := ((8082794833719401 : Rat) / 10000000000000000)
def block389W2 : Rat := ((10376311987954391 : Rat) / 250000000000000000)
def block389W3 : Rat := ((3408093925587421 : Rat) / 20000000000000000)
def block389W4 : Rat := ((7289432713918531 : Rat) / 50000000000000000)
def block389S1 : Rat := ((18174751 : Rat) / 10000000)
def block389S2 : Rat := ((511587 : Rat) / 200000)
def block389S3 : Rat := ((1060231636428571429 : Rat) / 400000000000000000)
def block389S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block389V (y : ℝ) : ℝ :=
  ratPotential block389W1 block389W2 block389W3 block389W4 block389S1 block389S2 block389S3 block389S4 y

def block389LeftParamsCertificate : Bool :=
  allBoxesSameParams block389LeftBoxes block389W1 block389W2 block389W3 block389W4 block389S1 block389S2 block389S3 block389S4

theorem block389LeftParamsCertificate_eq_true :
    block389LeftParamsCertificate = true := by
  native_decide

theorem block389_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block389LeftL : ℝ) (block389LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block389S1 : ℝ))
    (hy2ne : y ≠ (block389S2 : ℝ))
    (hy3ne : y ≠ (block389S3 : ℝ))
    (hy4ne : y ≠ (block389S4 : ℝ)) :
    0 < block389V y := by
  have hcert := block389LeftCertificate_eq_true
  unfold block389LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block389LeftBoxes) (lo := block389LeftL) (hi := block389LeftR)
    (w1 := block389W1) (w2 := block389W2) (w3 := block389W3) (w4 := block389W4)
    (s1 := block389S1) (s2 := block389S2) (s3 := block389S3) (s4 := block389S4)
    hboxes hcover block389LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block389RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block389RightChunk000 block389W1 block389W2 block389W3 block389W4 block389S1 block389S2 block389S3 block389S4

theorem block389RightChunk000ParamsCertificate_eq_true :
    block389RightChunk000ParamsCertificate = true := by
  native_decide

theorem block389_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block389RightChunk000L : ℝ) (block389RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block389S1 : ℝ))
    (hy2ne : y ≠ (block389S2 : ℝ))
    (hy3ne : y ≠ (block389S3 : ℝ))
    (hy4ne : y ≠ (block389S4 : ℝ)) :
    0 < block389V y := by
  have hcert := block389RightChunk000Certificate_eq_true
  unfold block389RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block389RightChunk000) (lo := block389RightChunk000L) (hi := block389RightChunk000R)
    (w1 := block389W1) (w2 := block389W2) (w3 := block389W3) (w4 := block389W4)
    (s1 := block389S1) (s2 := block389S2) (s3 := block389S3) (s4 := block389S4)
    hboxes hcover block389RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block389RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block389RightChunk001 block389W1 block389W2 block389W3 block389W4 block389S1 block389S2 block389S3 block389S4

theorem block389RightChunk001ParamsCertificate_eq_true :
    block389RightChunk001ParamsCertificate = true := by
  native_decide

theorem block389_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block389RightChunk001L : ℝ) (block389RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block389S1 : ℝ))
    (hy2ne : y ≠ (block389S2 : ℝ))
    (hy3ne : y ≠ (block389S3 : ℝ))
    (hy4ne : y ≠ (block389S4 : ℝ)) :
    0 < block389V y := by
  have hcert := block389RightChunk001Certificate_eq_true
  unfold block389RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block389RightChunk001) (lo := block389RightChunk001L) (hi := block389RightChunk001R)
    (w1 := block389W1) (w2 := block389W2) (w3 := block389W3) (w4 := block389W4)
    (s1 := block389S1) (s2 := block389S2) (s3 := block389S3) (s4 := block389S4)
    hboxes hcover block389RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block389_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block389RightL : ℝ) (block389RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block389S1 : ℝ))
    (hy2ne : y ≠ (block389S2 : ℝ))
    (hy3ne : y ≠ (block389S3 : ℝ))
    (hy4ne : y ≠ (block389S4 : ℝ)) :
    0 < block389V y := by
  by_cases h0 : y ≤ (block389RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block389RightChunk000L : ℝ) (block389RightChunk000R : ℝ) := by
      have hL : (block389RightChunk000L : ℝ) = (block389RightL : ℝ) := by
        norm_num [block389RightChunk000L, block389RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block389_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block389RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block389RightChunk001L : ℝ) = (block389RightChunk000R : ℝ) := by
      norm_num [block389RightChunk001L, block389RightChunk000R]
    have hR : (block389RightChunk001R : ℝ) = (block389RightR : ℝ) := by
      norm_num [block389RightChunk001R, block389RightR]
    have hyc : y ∈ Icc (block389RightChunk001L : ℝ) (block389RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block389_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block389_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block389LeftL : ℝ) (block389LeftR : ℝ) →
    y ≠ 0 → y ≠ (block389S1 : ℝ) → y ≠ (block389S2 : ℝ) →
    y ≠ (block389S3 : ℝ) → y ≠ (block389S4 : ℝ) → 0 < block389V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block389RightL : ℝ) (block389RightR : ℝ) →
    y ≠ 0 → y ≠ (block389S1 : ℝ) → y ≠ (block389S2 : ℝ) →
    y ≠ (block389S3 : ℝ) → y ≠ (block389S4 : ℝ) → 0 < block389V y)

theorem block389_reallog_certificate_proof :
    block389_reallog_certificate := by
  exact ⟨block389_left_V_pos, block389_right_V_pos⟩

end Block389
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block389.block389V
#check Erdos1038Lean.M1817475.Block389.block389_left_V_pos
#check Erdos1038Lean.M1817475.Block389.block389_right_V_pos
#check Erdos1038Lean.M1817475.Block389.block389_reallog_certificate_proof
