/-
Self-contained Lean4Web paste file.
Block 338 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block338

def block338LeftL : Rat := ((37560176339285714431 : Rat) / 50000000000000000000)
def block338LeftR : Rat := ((18784975446428571501 : Rat) / 25000000000000000000)
def block338RightL : Rat := ((87560176339285714431 : Rat) / 50000000000000000000)
def block338RightR : Rat := ((68784975446428571501 : Rat) / 25000000000000000000)

def block338LeftBoxes : List RatBox := [
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37560176339285714431 : Rat) / 50000000000000000000), R := ((18784975446428571501 : Rat) / 25000000000000000000), D0 := ((18784975446428571501 : Rat) / 25000000000000000000), D1 := ((53313578660714285569 : Rat) / 50000000000000000000), D2 := ((90336573660714285569 : Rat) / 50000000000000000000), D3 := ((23991445669642857109 : Rat) / 12500000000000000000), D4 := ((101058330089285709167 : Rat) / 50000000000000000000), LB := ((12800898749194961 : Rat) / 2000000000000000000) }
]

def block338LeftCertificate : Bool :=
  allBoxesValid block338LeftBoxes &&
  coversFromBool block338LeftBoxes block338LeftL block338LeftR

theorem block338LeftCertificate_eq_true :
    block338LeftCertificate = true := by
  native_decide

def block338RightChunk000 : List RatBox := [
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87560176339285714431 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3313578660714285569 : Rat) / 50000000000000000000), D2 := ((40336573660714285569 : Rat) / 50000000000000000000), D3 := ((11491445669642857109 : Rat) / 12500000000000000000), D4 := ((51058330089285709167 : Rat) / 50000000000000000000), LB := ((9753552052335309 : Rat) / 5000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42652204017857142867 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((18662943164774853 : Rat) / 100000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24140706517857142867 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((602049659347443 : Rat) / 5000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19512832142857142867 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((1596370726849193 : Rat) / 20000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17198894955357142867 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((19643852211057883 : Rat) / 1000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14884957767857142867 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((464481307562517 : Rat) / 25000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13727989174107142867 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((5405027206407849 : Rat) / 250000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((13149504877232142867 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((6402732642359507 : Rat) / 500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12571020580357142867 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((506014980686087 : Rat) / 100000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11992536283482142867 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((9494372719389493 : Rat) / 1000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11703294135044642867 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((410144629995007 : Rat) / 62500000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11414051986607142867 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((3953170515020171 : Rat) / 1000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11124809838169642867 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((4206309062183 : Rat) / 2500000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10835567689732142867 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((20604773027739 : Rat) / 4000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10690946615513392867 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((862740280597657 : Rat) / 200000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10546325541294642867 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((7146864034683953 : Rat) / 2000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10401704467075892867 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((117339118188039 : Rat) / 40000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10257083392857142867 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((958874036336399 : Rat) / 400000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10112462318638392867 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((123011339408707 : Rat) / 62500000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9967841244419642867 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((8252054046572199 : Rat) / 5000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9823220170200892867 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((72408605373879 : Rat) / 50000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9678599095982142867 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((6830825595217499 : Rat) / 5000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9533978021763392867 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((14095445072091761 : Rat) / 10000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9389356947544642867 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((989989783947761 : Rat) / 625000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9244735873325892867 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((18957507083424419 : Rat) / 10000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9100114799107142867 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((11758998916186203 : Rat) / 5000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8955493724888392867 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((591976229730673 : Rat) / 200000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8810872650669642867 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((1864337717494377 : Rat) / 500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8666251576450892867 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((291747407063659 : Rat) / 62500000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8521630502232142867 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((1777393959654927 : Rat) / 2500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8232388353794642867 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((35851734157024973 : Rat) / 10000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7943146205357142867 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((3681871666871603 : Rat) / 500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7653904056919642867 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((6109881059533223 : Rat) / 500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7364661908482142867 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((4286287630311303 : Rat) / 500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6786177611607142867 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((1898150849988671 : Rat) / 250000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028803209017857142867 : Rat) / 400000000000000000000), D0 := ((1028803209017857142867 : Rat) / 400000000000000000000), D1 := ((301813169017857142867 : Rat) / 400000000000000000000), D2 := ((5629209017857142867 : Rat) / 400000000000000000000), D3 := ((5629209017857142867 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((12361078989225241 : Rat) / 250000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028803209017857142867 : Rat) / 400000000000000000000), R := ((517216209017857142867 : Rat) / 200000000000000000000), D0 := ((517216209017857142867 : Rat) / 200000000000000000000), D1 := ((153721189017857142867 : Rat) / 200000000000000000000), D2 := ((5629209017857142867 : Rat) / 200000000000000000000), D3 := ((39404463125000000069 : Rat) / 400000000000000000000), D4 := ((80144842410714245917 : Rat) / 400000000000000000000), LB := ((2259856012069933 : Rat) / 100000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517216209017857142867 : Rat) / 200000000000000000000), R := ((1040061627053571428601 : Rat) / 400000000000000000000), D0 := ((1040061627053571428601 : Rat) / 400000000000000000000), D1 := ((313071587053571428601 : Rat) / 400000000000000000000), D2 := ((16887627053571428601 : Rat) / 400000000000000000000), D3 := ((16887627053571428601 : Rat) / 200000000000000000000), D4 := ((1490312667857142061 : Rat) / 8000000000000000000), LB := ((13433929611325501 : Rat) / 1000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1040061627053571428601 : Rat) / 400000000000000000000), R := ((261422709017857142867 : Rat) / 100000000000000000000), D0 := ((261422709017857142867 : Rat) / 100000000000000000000), D1 := ((79675199017857142867 : Rat) / 100000000000000000000), D2 := ((5629209017857142867 : Rat) / 100000000000000000000), D3 := ((5629209017857142867 : Rat) / 80000000000000000000), D4 := ((68886424374999960183 : Rat) / 400000000000000000000), LB := ((471122487786739 : Rat) / 31250000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261422709017857142867 : Rat) / 100000000000000000000), R := ((210264009017857142867 : Rat) / 80000000000000000000), D0 := ((210264009017857142867 : Rat) / 80000000000000000000), D1 := ((64866001017857142867 : Rat) / 80000000000000000000), D2 := ((5629209017857142867 : Rat) / 80000000000000000000), D3 := ((5629209017857142867 : Rat) / 100000000000000000000), D4 := ((15814303839285704329 : Rat) / 100000000000000000000), LB := ((13479213641353377 : Rat) / 500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((210264009017857142867 : Rat) / 80000000000000000000), R := ((528474627053571428601 : Rat) / 200000000000000000000), D0 := ((528474627053571428601 : Rat) / 200000000000000000000), D1 := ((164979607053571428601 : Rat) / 200000000000000000000), D2 := ((16887627053571428601 : Rat) / 200000000000000000000), D3 := ((16887627053571428601 : Rat) / 400000000000000000000), D4 := ((57628006339285674449 : Rat) / 400000000000000000000), LB := ((2578224405199689 : Rat) / 50000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528474627053571428601 : Rat) / 200000000000000000000), R := ((133525959017857142867 : Rat) / 50000000000000000000), D0 := ((133525959017857142867 : Rat) / 50000000000000000000), D1 := ((42652204017857142867 : Rat) / 50000000000000000000), D2 := ((5629209017857142867 : Rat) / 50000000000000000000), D3 := ((5629209017857142867 : Rat) / 200000000000000000000), D4 := ((25999398660714265791 : Rat) / 200000000000000000000), LB := ((691247593412469 : Rat) / 10000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133525959017857142867 : Rat) / 50000000000000000000), R := ((538147827946428571603 : Rat) / 200000000000000000000), D0 := ((538147827946428571603 : Rat) / 200000000000000000000), D1 := ((174652807946428571603 : Rat) / 200000000000000000000), D2 := ((26560827946428571603 : Rat) / 200000000000000000000), D3 := ((808798375000000027 : Rat) / 40000000000000000000), D4 := ((5092547410714280731 : Rat) / 50000000000000000000), LB := ((11354325602794013 : Rat) / 100000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((538147827946428571603 : Rat) / 200000000000000000000), R := ((271095909910714285869 : Rat) / 100000000000000000000), D0 := ((271095909910714285869 : Rat) / 100000000000000000000), D1 := ((89348399910714285869 : Rat) / 100000000000000000000), D2 := ((15302409910714285869 : Rat) / 100000000000000000000), D3 := ((808798375000000027 : Rat) / 20000000000000000000), D4 := ((16326197767857122789 : Rat) / 200000000000000000000), LB := ((7665323523471157 : Rat) / 1000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((271095909910714285869 : Rat) / 100000000000000000000), R := ((2172811271160714287087 : Rat) / 800000000000000000000), D0 := ((2172811271160714287087 : Rat) / 800000000000000000000), D1 := ((718831191160714287087 : Rat) / 800000000000000000000), D2 := ((126463271160714287087 : Rat) / 800000000000000000000), D3 := ((7279185375000000243 : Rat) / 160000000000000000000), D4 := ((6141102946428561327 : Rat) / 100000000000000000000), LB := ((10508967561015603 : Rat) / 500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2172811271160714287087 : Rat) / 800000000000000000000), R := ((1088427631517857143611 : Rat) / 400000000000000000000), D0 := ((1088427631517857143611 : Rat) / 400000000000000000000), D1 := ((361437591517857143611 : Rat) / 400000000000000000000), D2 := ((65253631517857143611 : Rat) / 400000000000000000000), D3 := ((808798375000000027 : Rat) / 16000000000000000000), D4 := ((45084831696428490481 : Rat) / 800000000000000000000), LB := ((558263834434667 : Rat) / 62500000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1088427631517857143611 : Rat) / 400000000000000000000), R := ((4357754517946428574579 : Rat) / 1600000000000000000000), D0 := ((4357754517946428574579 : Rat) / 1600000000000000000000), D1 := ((1449794357946428574579 : Rat) / 1600000000000000000000), D2 := ((265058517946428574579 : Rat) / 1600000000000000000000), D3 := ((16984765875000000567 : Rat) / 320000000000000000000), D4 := ((20520419910714245173 : Rat) / 400000000000000000000), LB := ((328164379237739 : Rat) / 31250000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4357754517946428574579 : Rat) / 1600000000000000000000), R := ((2180899254910714287357 : Rat) / 800000000000000000000), D0 := ((2180899254910714287357 : Rat) / 800000000000000000000), D1 := ((726919174910714287357 : Rat) / 800000000000000000000), D2 := ((134551254910714287357 : Rat) / 800000000000000000000), D3 := ((8896782125000000297 : Rat) / 160000000000000000000), D4 := ((78037687767856980557 : Rat) / 1600000000000000000000), LB := ((6443985945077613 : Rat) / 1000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2180899254910714287357 : Rat) / 800000000000000000000), R := ((4365842501696428574849 : Rat) / 1600000000000000000000), D0 := ((4365842501696428574849 : Rat) / 1600000000000000000000), D1 := ((1457882341696428574849 : Rat) / 1600000000000000000000), D2 := ((273146501696428574849 : Rat) / 1600000000000000000000), D3 := ((18602362625000000621 : Rat) / 320000000000000000000), D4 := ((36996847946428490211 : Rat) / 800000000000000000000), LB := ((615188283297341 : Rat) / 200000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4365842501696428574849 : Rat) / 1600000000000000000000), R := ((546235811696428571873 : Rat) / 200000000000000000000), D0 := ((546235811696428571873 : Rat) / 200000000000000000000), D1 := ((182740791696428571873 : Rat) / 200000000000000000000), D2 := ((34648811696428571873 : Rat) / 200000000000000000000), D3 := ((2426395125000000081 : Rat) / 40000000000000000000), D4 := ((69949704017856980287 : Rat) / 1600000000000000000000), LB := ((20637664211978213 : Rat) / 50000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546235811696428571873 : Rat) / 200000000000000000000), R := ((8743816979017857150103 : Rat) / 3200000000000000000000), D0 := ((8743816979017857150103 : Rat) / 3200000000000000000000), D1 := ((2927896659017857150103 : Rat) / 3200000000000000000000), D2 := ((558424979017857150103 : Rat) / 3200000000000000000000), D3 := ((39631120375000001323 : Rat) / 640000000000000000000), D4 := ((8238214017857122519 : Rat) / 200000000000000000000), LB := ((1754302081659359 : Rat) / 500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8743816979017857150103 : Rat) / 3200000000000000000000), R := ((4373930485446428575119 : Rat) / 1600000000000000000000), D0 := ((4373930485446428575119 : Rat) / 1600000000000000000000), D1 := ((1465970325446428575119 : Rat) / 1600000000000000000000), D2 := ((281234485446428575119 : Rat) / 1600000000000000000000), D3 := ((808798375000000027 : Rat) / 12800000000000000000), D4 := ((127767432410713960169 : Rat) / 3200000000000000000000), LB := ((2765507928818023 : Rat) / 1000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4373930485446428575119 : Rat) / 1600000000000000000000), R := ((8751904962767857150373 : Rat) / 3200000000000000000000), D0 := ((8751904962767857150373 : Rat) / 3200000000000000000000), D1 := ((2935984642767857150373 : Rat) / 3200000000000000000000), D2 := ((566512962767857150373 : Rat) / 3200000000000000000000), D3 := ((41248717125000001377 : Rat) / 640000000000000000000), D4 := ((61861720267856980017 : Rat) / 1600000000000000000000), LB := ((4445678725139679 : Rat) / 2000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8751904962767857150373 : Rat) / 3200000000000000000000), R := ((2188987238660714287627 : Rat) / 800000000000000000000), D0 := ((2188987238660714287627 : Rat) / 800000000000000000000), D1 := ((735007158660714287627 : Rat) / 800000000000000000000), D2 := ((142639238660714287627 : Rat) / 800000000000000000000), D3 := ((10514378875000000351 : Rat) / 160000000000000000000), D4 := ((119679448660713959899 : Rat) / 3200000000000000000000), LB := ((4718653932541117 : Rat) / 2500000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2188987238660714287627 : Rat) / 800000000000000000000), R := ((8759992946517857150643 : Rat) / 3200000000000000000000), D0 := ((8759992946517857150643 : Rat) / 3200000000000000000000), D1 := ((2944072626517857150643 : Rat) / 3200000000000000000000), D2 := ((574600946517857150643 : Rat) / 3200000000000000000000), D3 := ((42866313875000001431 : Rat) / 640000000000000000000), D4 := ((28908864196428489941 : Rat) / 800000000000000000000), LB := ((17673125975403159 : Rat) / 10000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8759992946517857150643 : Rat) / 3200000000000000000000), R := ((4382018469196428575389 : Rat) / 1600000000000000000000), D0 := ((4382018469196428575389 : Rat) / 1600000000000000000000), D1 := ((1474058309196428575389 : Rat) / 1600000000000000000000), D2 := ((289322469196428575389 : Rat) / 1600000000000000000000), D3 := ((21837556125000000729 : Rat) / 320000000000000000000), D4 := ((111591464910713959629 : Rat) / 3200000000000000000000), LB := ((9357651756039531 : Rat) / 5000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4382018469196428575389 : Rat) / 1600000000000000000000), R := ((8768080930267857150913 : Rat) / 3200000000000000000000), D0 := ((8768080930267857150913 : Rat) / 3200000000000000000000), D1 := ((2952160610267857150913 : Rat) / 3200000000000000000000), D2 := ((582688930267857150913 : Rat) / 3200000000000000000000), D3 := ((8896782125000000297 : Rat) / 128000000000000000000), D4 := ((53773736517856979747 : Rat) / 1600000000000000000000), LB := ((442120664137291 : Rat) / 200000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8768080930267857150913 : Rat) / 3200000000000000000000), R := ((1096515615267857143881 : Rat) / 400000000000000000000), D0 := ((1096515615267857143881 : Rat) / 400000000000000000000), D1 := ((369525575267857143881 : Rat) / 400000000000000000000), D2 := ((73341615267857143881 : Rat) / 400000000000000000000), D3 := ((5661588625000000189 : Rat) / 80000000000000000000), D4 := ((103503481160713959359 : Rat) / 3200000000000000000000), LB := ((2796552627469029 : Rat) / 1000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1096515615267857143881 : Rat) / 400000000000000000000), R := ((8776168914017857151183 : Rat) / 3200000000000000000000), D0 := ((8776168914017857151183 : Rat) / 3200000000000000000000), D1 := ((2960248594017857151183 : Rat) / 3200000000000000000000), D2 := ((590776914017857151183 : Rat) / 3200000000000000000000), D3 := ((46101507375000001539 : Rat) / 640000000000000000000), D4 := ((12432436160714244903 : Rat) / 400000000000000000000), LB := ((910788173281829 : Rat) / 250000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8776168914017857151183 : Rat) / 3200000000000000000000), R := ((4390106452946428575659 : Rat) / 1600000000000000000000), D0 := ((4390106452946428575659 : Rat) / 1600000000000000000000), D1 := ((1482146292946428575659 : Rat) / 1600000000000000000000), D2 := ((297410452946428575659 : Rat) / 1600000000000000000000), D3 := ((23455152875000000783 : Rat) / 320000000000000000000), D4 := ((95415497410713959089 : Rat) / 3200000000000000000000), LB := ((297887492281889 : Rat) / 62500000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4390106452946428575659 : Rat) / 1600000000000000000000), R := ((2197075222410714287897 : Rat) / 800000000000000000000), D0 := ((2197075222410714287897 : Rat) / 800000000000000000000), D1 := ((743095142410714287897 : Rat) / 800000000000000000000), D2 := ((150727222410714287897 : Rat) / 800000000000000000000), D3 := ((2426395125000000081 : Rat) / 32000000000000000000), D4 := ((45685752767856979477 : Rat) / 1600000000000000000000), LB := ((8460988959690663 : Rat) / 5000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2197075222410714287897 : Rat) / 800000000000000000000), R := ((4398194436696428575929 : Rat) / 1600000000000000000000), D0 := ((4398194436696428575929 : Rat) / 1600000000000000000000), D1 := ((1490234276696428575929 : Rat) / 1600000000000000000000), D2 := ((305498436696428575929 : Rat) / 1600000000000000000000), D3 := ((25072749625000000837 : Rat) / 320000000000000000000), D4 := ((20820880446428489671 : Rat) / 800000000000000000000), LB := ((5585708644429421 : Rat) / 1000000000000000000) },
  { w1 := ((2329232673137199 : Rat) / 2500000000000000), w2 := ((47492180344329 : Rat) / 1000000000000000), w3 := ((7268655608047789 : Rat) / 50000000000000000), w4 := ((2750185185162643 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133525959017857142867 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4398194436696428575929 : Rat) / 1600000000000000000000), R := ((68784975446428571501 : Rat) / 25000000000000000000), D0 := ((68784975446428571501 : Rat) / 25000000000000000000), D1 := ((23348097946428571501 : Rat) / 25000000000000000000), D2 := ((4836600446428571501 : Rat) / 25000000000000000000), D3 := ((808798375000000027 : Rat) / 10000000000000000000), D4 := ((37597769017856979207 : Rat) / 1600000000000000000000), LB := ((10949613473103303 : Rat) / 1000000000000000000) }
]

def block338RightChunk000L : Rat := ((87560176339285714431 : Rat) / 50000000000000000000)
def block338RightChunk000R : Rat := ((68784975446428571501 : Rat) / 25000000000000000000)

def block338RightChunk000Certificate : Bool :=
  allBoxesValid block338RightChunk000 &&
  coversFromBool block338RightChunk000 block338RightChunk000L block338RightChunk000R

theorem block338RightChunk000Certificate_eq_true :
    block338RightChunk000Certificate = true := by
  native_decide

def block338RightChainCertificate : Bool :=
  decide (
    block338RightL = ((87560176339285714431 : Rat) / 50000000000000000000) /\
    ((68784975446428571501 : Rat) / 25000000000000000000) = block338RightR)

theorem block338RightChainCertificate_eq_true :
    block338RightChainCertificate = true := by
  native_decide

def block338LeftBoxCount : Nat := boxCount block338LeftBoxes
def block338RightBoxCount : Nat := 63

def block338_rational_certificate : Prop :=
    block338LeftCertificate = true /\
    block338RightChainCertificate = true /\
    block338RightChunk000Certificate = true

theorem block338_rational_certificate_proof :
    block338_rational_certificate := by
  exact ⟨block338LeftCertificate_eq_true, block338RightChainCertificate_eq_true, block338RightChunk000Certificate_eq_true⟩

end Block338
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block338

open Set

def block338W1 : Rat := ((2329232673137199 : Rat) / 2500000000000000)
def block338W2 : Rat := ((47492180344329 : Rat) / 1000000000000000)
def block338W3 : Rat := ((7268655608047789 : Rat) / 50000000000000000)
def block338W4 : Rat := ((2750185185162643 : Rat) / 20000000000000000)
def block338S1 : Rat := ((18174751 : Rat) / 10000000)
def block338S2 : Rat := ((511587 : Rat) / 200000)
def block338S3 : Rat := ((133525959017857142867 : Rat) / 50000000000000000000)
def block338S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block338V (y : ℝ) : ℝ :=
  ratPotential block338W1 block338W2 block338W3 block338W4 block338S1 block338S2 block338S3 block338S4 y

def block338LeftParamsCertificate : Bool :=
  allBoxesSameParams block338LeftBoxes block338W1 block338W2 block338W3 block338W4 block338S1 block338S2 block338S3 block338S4

theorem block338LeftParamsCertificate_eq_true :
    block338LeftParamsCertificate = true := by
  native_decide

theorem block338_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block338LeftL : ℝ) (block338LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block338S1 : ℝ))
    (hy2ne : y ≠ (block338S2 : ℝ))
    (hy3ne : y ≠ (block338S3 : ℝ))
    (hy4ne : y ≠ (block338S4 : ℝ)) :
    0 < block338V y := by
  have hcert := block338LeftCertificate_eq_true
  unfold block338LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block338LeftBoxes) (lo := block338LeftL) (hi := block338LeftR)
    (w1 := block338W1) (w2 := block338W2) (w3 := block338W3) (w4 := block338W4)
    (s1 := block338S1) (s2 := block338S2) (s3 := block338S3) (s4 := block338S4)
    hboxes hcover block338LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block338RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block338RightChunk000 block338W1 block338W2 block338W3 block338W4 block338S1 block338S2 block338S3 block338S4

theorem block338RightChunk000ParamsCertificate_eq_true :
    block338RightChunk000ParamsCertificate = true := by
  native_decide

theorem block338_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block338RightChunk000L : ℝ) (block338RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block338S1 : ℝ))
    (hy2ne : y ≠ (block338S2 : ℝ))
    (hy3ne : y ≠ (block338S3 : ℝ))
    (hy4ne : y ≠ (block338S4 : ℝ)) :
    0 < block338V y := by
  have hcert := block338RightChunk000Certificate_eq_true
  unfold block338RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block338RightChunk000) (lo := block338RightChunk000L) (hi := block338RightChunk000R)
    (w1 := block338W1) (w2 := block338W2) (w3 := block338W3) (w4 := block338W4)
    (s1 := block338S1) (s2 := block338S2) (s3 := block338S3) (s4 := block338S4)
    hboxes hcover block338RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block338_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block338RightL : ℝ) (block338RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block338S1 : ℝ))
    (hy2ne : y ≠ (block338S2 : ℝ))
    (hy3ne : y ≠ (block338S3 : ℝ))
    (hy4ne : y ≠ (block338S4 : ℝ)) :
    0 < block338V y := by
  have hL : (block338RightChunk000L : ℝ) = (block338RightL : ℝ) := by
    norm_num [block338RightChunk000L, block338RightL]
  have hR : (block338RightChunk000R : ℝ) = (block338RightR : ℝ) := by
    norm_num [block338RightChunk000R, block338RightR]
  have hyc : y ∈ Icc (block338RightChunk000L : ℝ) (block338RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block338_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block338_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block338LeftL : ℝ) (block338LeftR : ℝ) →
    y ≠ 0 → y ≠ (block338S1 : ℝ) → y ≠ (block338S2 : ℝ) →
    y ≠ (block338S3 : ℝ) → y ≠ (block338S4 : ℝ) → 0 < block338V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block338RightL : ℝ) (block338RightR : ℝ) →
    y ≠ 0 → y ≠ (block338S1 : ℝ) → y ≠ (block338S2 : ℝ) →
    y ≠ (block338S3 : ℝ) → y ≠ (block338S4 : ℝ) → 0 < block338V y)

theorem block338_reallog_certificate_proof :
    block338_reallog_certificate := by
  exact ⟨block338_left_V_pos, block338_right_V_pos⟩

end Block338
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block338.block338V
#check Erdos1038Lean.M1817475.Block338.block338_left_V_pos
#check Erdos1038Lean.M1817475.Block338.block338_right_V_pos
#check Erdos1038Lean.M1817475.Block338.block338_reallog_certificate_proof
