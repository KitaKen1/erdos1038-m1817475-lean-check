/-
Self-contained Lean4Web paste file.
Block 297 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block297

def block297LeftL : Rat := ((18980466517857142921 : Rat) / 25000000000000000000)
def block297LeftR : Rat := ((37970707589285714413 : Rat) / 50000000000000000000)
def block297RightL : Rat := ((43980466517857142921 : Rat) / 25000000000000000000)
def block297RightR : Rat := ((137970707589285714413 : Rat) / 50000000000000000000)

def block297LeftBoxes : List RatBox := [
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((18980466517857142921 : Rat) / 25000000000000000000), R := ((37970707589285714413 : Rat) / 50000000000000000000), D0 := ((37970707589285714413 : Rat) / 50000000000000000000), D1 := ((26456410982142857079 : Rat) / 25000000000000000000), D2 := ((44967908482142857079 : Rat) / 25000000000000000000), D3 := ((98086860803571428343 : Rat) / 50000000000000000000), D4 := ((1273370225446428507 : Rat) / 625000000000000000), LB := ((961291636306677 : Rat) / 125000000000000000) }
]

def block297LeftCertificate : Bool :=
  allBoxesValid block297LeftBoxes &&
  coversFromBool block297LeftBoxes block297LeftL block297LeftR

theorem block297LeftCertificate_eq_true :
    block297LeftCertificate = true := by
  native_decide

def block297RightChunk000 : List RatBox := [
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((43980466517857142921 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1456410982142857079 : Rat) / 25000000000000000000), D2 := ((19967908482142857079 : Rat) / 25000000000000000000), D3 := ((48086860803571428343 : Rat) / 50000000000000000000), D4 := ((648370225446428507 : Rat) / 625000000000000000), LB := ((8935001845211 : Rat) / 3906250000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((24478398035714283201 : Rat) / 25000000000000000000), LB := ((2593397653642357 : Rat) / 10000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((15222649285714283201 : Rat) / 25000000000000000000), LB := ((8409354169432473 : Rat) / 50000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((4406933392857142837 : Rat) / 10000000000000000000), D4 := ((12908712098214283201 : Rat) / 25000000000000000000), LB := ((9673740396188901 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((10594774910714283201 : Rat) / 25000000000000000000), LB := ((2586536817639911 : Rat) / 62500000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((3249964799107142837 : Rat) / 10000000000000000000), D4 := ((10016290613839283201 : Rat) / 25000000000000000000), LB := ((170184742649101 : Rat) / 10000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((3018571080357142837 : Rat) / 10000000000000000000), D4 := ((9437806316964283201 : Rat) / 25000000000000000000), LB := ((1006180788935207 : Rat) / 50000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2902874220982142837 : Rat) / 10000000000000000000), D4 := ((9148564168526783201 : Rat) / 25000000000000000000), LB := ((11107613762562307 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2787177361607142837 : Rat) / 10000000000000000000), D4 := ((8859322020089283201 : Rat) / 25000000000000000000), LB := ((3263856444159663 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2671480502232142837 : Rat) / 10000000000000000000), D4 := ((8570079871651783201 : Rat) / 25000000000000000000), LB := ((4039680308149579 : Rat) / 500000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2613632072544642837 : Rat) / 10000000000000000000), D4 := ((8425458797433033201 : Rat) / 25000000000000000000), LB := ((653426068395857 : Rat) / 125000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((8280837723214283201 : Rat) / 25000000000000000000), LB := ((13747958758624501 : Rat) / 5000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((2497935213169642837 : Rat) / 10000000000000000000), D4 := ((8136216648995533201 : Rat) / 25000000000000000000), LB := ((1676328743942107 : Rat) / 2500000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((2440086783482142837 : Rat) / 10000000000000000000), D4 := ((7991595574776783201 : Rat) / 25000000000000000000), LB := ((457498925287253 : Rat) / 100000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((2411162568638392837 : Rat) / 10000000000000000000), D4 := ((7919285037667408201 : Rat) / 25000000000000000000), LB := ((487528086422509 : Rat) / 125000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((2382238353794642837 : Rat) / 10000000000000000000), D4 := ((7846974500558033201 : Rat) / 25000000000000000000), LB := ((33463225199754643 : Rat) / 10000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((2353314138950892837 : Rat) / 10000000000000000000), D4 := ((7774663963448658201 : Rat) / 25000000000000000000), LB := ((14594350116899357 : Rat) / 5000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((2324389924107142837 : Rat) / 10000000000000000000), D4 := ((7702353426339283201 : Rat) / 25000000000000000000), LB := ((6560198801412731 : Rat) / 2500000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((2295465709263392837 : Rat) / 10000000000000000000), D4 := ((7630042889229908201 : Rat) / 25000000000000000000), LB := ((24688901364001703 : Rat) / 10000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((2266541494419642837 : Rat) / 10000000000000000000), D4 := ((7557732352120533201 : Rat) / 25000000000000000000), LB := ((2461091934020221 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((2237617279575892837 : Rat) / 10000000000000000000), D4 := ((7485421815011158201 : Rat) / 25000000000000000000), LB := ((326184828989759 : Rat) / 125000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((6407626219 : Rat) / 2560000000), D0 := ((6407626219 : Rat) / 2560000000), D1 := ((1754889963 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((2208693064732142837 : Rat) / 10000000000000000000), D4 := ((7413111277901783201 : Rat) / 25000000000000000000), LB := ((29240372557399197 : Rat) / 10000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6407626219 : Rat) / 2560000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((140687381 : Rat) / 2560000000), D3 := ((2179768849888392837 : Rat) / 10000000000000000000), D4 := ((7340800740792408201 : Rat) / 25000000000000000000), LB := ((17080930370702019 : Rat) / 5000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((6422435417 : Rat) / 2560000000), D0 := ((6422435417 : Rat) / 2560000000), D1 := ((1769699161 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((2150844635044642837 : Rat) / 10000000000000000000), D4 := ((7268490203683033201 : Rat) / 25000000000000000000), LB := ((4099076466591911 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6422435417 : Rat) / 2560000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((125878183 : Rat) / 2560000000), D3 := ((2121920420200892837 : Rat) / 10000000000000000000), D4 := ((7196179666573658201 : Rat) / 25000000000000000000), LB := ((4987980638167577 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((7123869129464283201 : Rat) / 25000000000000000000), LB := ((7794640631385019 : Rat) / 10000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((2035147775669642837 : Rat) / 10000000000000000000), D4 := ((6979248055245533201 : Rat) / 25000000000000000000), LB := ((9506711753599073 : Rat) / 2500000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((647426761 : Rat) / 256000000), D0 := ((647426761 : Rat) / 256000000), D1 := ((910765677 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1977299345982142837 : Rat) / 10000000000000000000), D4 := ((6834626981026783201 : Rat) / 25000000000000000000), LB := ((502350146062841 : Rat) / 62500000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((647426761 : Rat) / 256000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 256000000), D3 := ((1919450916294642837 : Rat) / 10000000000000000000), D4 := ((6690005906808033201 : Rat) / 25000000000000000000), LB := ((1729037348960287 : Rat) / 125000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((1629673801 : Rat) / 640000000), D0 := ((1629673801 : Rat) / 640000000), D1 := ((466489737 : Rat) / 640000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((6545384832589283201 : Rat) / 25000000000000000000), LB := ((11460960562368783 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1629673801 : Rat) / 640000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 640000000), D3 := ((1745905627232142837 : Rat) / 10000000000000000000), D4 := ((6256142684151783201 : Rat) / 25000000000000000000), LB := ((3945727363928153 : Rat) / 100000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((410899808767857142837 : Rat) / 160000000000000000000), D0 := ((410899808767857142837 : Rat) / 160000000000000000000), D1 := ((120103792767857142837 : Rat) / 160000000000000000000), D2 := ((1630208767857142837 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((5966900535714283201 : Rat) / 25000000000000000000), LB := ((1152982678761899 : Rat) / 25000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((410899808767857142837 : Rat) / 160000000000000000000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 32000000000000000000), D4 := ((182789773303571348247 : Rat) / 800000000000000000000), LB := ((3850075079867371 : Rat) / 250000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((165338048767857142837 : Rat) / 64000000000000000000), D0 := ((165338048767857142837 : Rat) / 64000000000000000000), D1 := ((49019642367857142837 : Rat) / 64000000000000000000), D2 := ((1630208767857142837 : Rat) / 64000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((87319364732142817031 : Rat) / 400000000000000000000), LB := ((1564750883581667 : Rat) / 100000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((165338048767857142837 : Rat) / 64000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((44015636732142856599 : Rat) / 320000000000000000000), D4 := ((341126415089285553939 : Rat) / 1600000000000000000000), LB := ((8834298596261947 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((166487685624999919877 : Rat) / 800000000000000000000), LB := ((462271209983961 : Rat) / 125000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((332306306303571428511 : Rat) / 128000000000000000000), D0 := ((332306306303571428511 : Rat) / 128000000000000000000), D1 := ((99669493503571428511 : Rat) / 128000000000000000000), D2 := ((4890626303571428511 : Rat) / 128000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((324824327410714125569 : Rat) / 1600000000000000000000), LB := ((7075034798863733 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((332306306303571428511 : Rat) / 128000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((79880229624999999013 : Rat) / 640000000000000000000), D4 := ((641497610982142536953 : Rat) / 3200000000000000000000), LB := ((10917912731129853 : Rat) / 2000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((1664791949053571428229 : Rat) / 640000000000000000000), D0 := ((1664791949053571428229 : Rat) / 640000000000000000000), D1 := ((501607885053571428229 : Rat) / 640000000000000000000), D2 := ((27713549053571428229 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((39584160446428551423 : Rat) / 200000000000000000000), LB := ((414269697625369 : Rat) / 100000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1664791949053571428229 : Rat) / 640000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((76619812089285713339 : Rat) / 640000000000000000000), D4 := ((625195523303571108583 : Rat) / 3200000000000000000000), LB := ((15555303935108067 : Rat) / 5000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((308522239732142697199 : Rat) / 1600000000000000000000), LB := ((5880991496859389 : Rat) / 2500000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((608893435624999680213 : Rat) / 3200000000000000000000), LB := ((4644902039964427 : Rat) / 2500000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((150185597946428491507 : Rat) / 800000000000000000000), LB := ((2026807128393121 : Rat) / 1250000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((592591347946428251843 : Rat) / 3200000000000000000000), LB := ((2048285018184659 : Rat) / 1250000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((292220152053571268829 : Rat) / 1600000000000000000000), LB := ((148992756695129 : Rat) / 78125000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((576289260267856823473 : Rat) / 3200000000000000000000), LB := ((2426112442778461 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((71017277053571388661 : Rat) / 400000000000000000000), LB := ((31963617830879087 : Rat) / 10000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((559987172589285395103 : Rat) / 3200000000000000000000), LB := ((263747860753033 : Rat) / 62500000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((275918064374999840459 : Rat) / 1600000000000000000000), LB := ((1100073051465933 : Rat) / 200000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((543685084910713966733 : Rat) / 3200000000000000000000), LB := ((14084599995158209 : Rat) / 2000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((133883510267857063137 : Rat) / 800000000000000000000), LB := ((32292781903701107 : Rat) / 10000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((259615976696428412089 : Rat) / 1600000000000000000000), LB := ((7798957738688439 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((15716558303571418619 : Rat) / 100000000000000000000), LB := ((575736714643349 : Rat) / 200000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((117581422589285634767 : Rat) / 800000000000000000000), LB := ((9311404209496943 : Rat) / 500000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((54715189374999960291 : Rat) / 400000000000000000000), LB := ((20967223111382993 : Rat) / 1000000000000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((23282072767857123053 : Rat) / 200000000000000000000), LB := ((44919185610999 : Rat) / 781250000000000) },
  { w1 := ((5037343253966663 : Rat) / 5000000000000000), w2 := ((4450298804305717 : Rat) / 100000000000000000), w3 := ((5471571592499097 : Rat) / 20000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((137970707589285714413 : Rat) / 50000000000000000000), D0 := ((137970707589285714413 : Rat) / 50000000000000000000), D1 := ((47096952589285714413 : Rat) / 50000000000000000000), D2 := ((10073957589285714413 : Rat) / 50000000000000000000), D3 := ((480728437500000057 : Rat) / 12500000000000000000), D4 := ((3782757232142852217 : Rat) / 50000000000000000000), LB := ((1581712076337527 : Rat) / 200000000000000000) }
]

def block297RightChunk000L : Rat := ((43980466517857142921 : Rat) / 25000000000000000000)
def block297RightChunk000R : Rat := ((137970707589285714413 : Rat) / 50000000000000000000)

def block297RightChunk000Certificate : Bool :=
  allBoxesValid block297RightChunk000 &&
  coversFromBool block297RightChunk000 block297RightChunk000L block297RightChunk000R

theorem block297RightChunk000Certificate_eq_true :
    block297RightChunk000Certificate = true := by
  native_decide

def block297RightChainCertificate : Bool :=
  decide (
    block297RightL = ((43980466517857142921 : Rat) / 25000000000000000000) /\
    ((137970707589285714413 : Rat) / 50000000000000000000) = block297RightR)

theorem block297RightChainCertificate_eq_true :
    block297RightChainCertificate = true := by
  native_decide

def block297LeftBoxCount : Nat := boxCount block297LeftBoxes
def block297RightBoxCount : Nat := 57

def block297_rational_certificate : Prop :=
    block297LeftCertificate = true /\
    block297RightChainCertificate = true /\
    block297RightChunk000Certificate = true

theorem block297_rational_certificate_proof :
    block297_rational_certificate := by
  exact ⟨block297LeftCertificate_eq_true, block297RightChainCertificate_eq_true, block297RightChunk000Certificate_eq_true⟩

end Block297
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block297

open Set

def block297W1 : Rat := ((5037343253966663 : Rat) / 5000000000000000)
def block297W2 : Rat := ((4450298804305717 : Rat) / 100000000000000000)
def block297W3 : Rat := ((5471571592499097 : Rat) / 20000000000000000)
def block297W4 : Rat := (0 : Rat)
def block297S1 : Rat := ((18174751 : Rat) / 10000000)
def block297S2 : Rat := ((511587 : Rat) / 200000)
def block297S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block297S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block297V (y : ℝ) : ℝ :=
  ratPotential block297W1 block297W2 block297W3 block297W4 block297S1 block297S2 block297S3 block297S4 y

def block297LeftParamsCertificate : Bool :=
  allBoxesSameParams block297LeftBoxes block297W1 block297W2 block297W3 block297W4 block297S1 block297S2 block297S3 block297S4

theorem block297LeftParamsCertificate_eq_true :
    block297LeftParamsCertificate = true := by
  native_decide

theorem block297_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block297LeftL : ℝ) (block297LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block297S1 : ℝ))
    (hy2ne : y ≠ (block297S2 : ℝ))
    (hy3ne : y ≠ (block297S3 : ℝ))
    (hy4ne : y ≠ (block297S4 : ℝ)) :
    0 < block297V y := by
  have hcert := block297LeftCertificate_eq_true
  unfold block297LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block297LeftBoxes) (lo := block297LeftL) (hi := block297LeftR)
    (w1 := block297W1) (w2 := block297W2) (w3 := block297W3) (w4 := block297W4)
    (s1 := block297S1) (s2 := block297S2) (s3 := block297S3) (s4 := block297S4)
    hboxes hcover block297LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block297RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block297RightChunk000 block297W1 block297W2 block297W3 block297W4 block297S1 block297S2 block297S3 block297S4

theorem block297RightChunk000ParamsCertificate_eq_true :
    block297RightChunk000ParamsCertificate = true := by
  native_decide

theorem block297_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block297RightChunk000L : ℝ) (block297RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block297S1 : ℝ))
    (hy2ne : y ≠ (block297S2 : ℝ))
    (hy3ne : y ≠ (block297S3 : ℝ))
    (hy4ne : y ≠ (block297S4 : ℝ)) :
    0 < block297V y := by
  have hcert := block297RightChunk000Certificate_eq_true
  unfold block297RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block297RightChunk000) (lo := block297RightChunk000L) (hi := block297RightChunk000R)
    (w1 := block297W1) (w2 := block297W2) (w3 := block297W3) (w4 := block297W4)
    (s1 := block297S1) (s2 := block297S2) (s3 := block297S3) (s4 := block297S4)
    hboxes hcover block297RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block297_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block297RightL : ℝ) (block297RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block297S1 : ℝ))
    (hy2ne : y ≠ (block297S2 : ℝ))
    (hy3ne : y ≠ (block297S3 : ℝ))
    (hy4ne : y ≠ (block297S4 : ℝ)) :
    0 < block297V y := by
  have hL : (block297RightChunk000L : ℝ) = (block297RightL : ℝ) := by
    norm_num [block297RightChunk000L, block297RightL]
  have hR : (block297RightChunk000R : ℝ) = (block297RightR : ℝ) := by
    norm_num [block297RightChunk000R, block297RightR]
  have hyc : y ∈ Icc (block297RightChunk000L : ℝ) (block297RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block297_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block297_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block297LeftL : ℝ) (block297LeftR : ℝ) →
    y ≠ 0 → y ≠ (block297S1 : ℝ) → y ≠ (block297S2 : ℝ) →
    y ≠ (block297S3 : ℝ) → y ≠ (block297S4 : ℝ) → 0 < block297V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block297RightL : ℝ) (block297RightR : ℝ) →
    y ≠ 0 → y ≠ (block297S1 : ℝ) → y ≠ (block297S2 : ℝ) →
    y ≠ (block297S3 : ℝ) → y ≠ (block297S4 : ℝ) → 0 < block297V y)

theorem block297_reallog_certificate_proof :
    block297_reallog_certificate := by
  exact ⟨block297_left_V_pos, block297_right_V_pos⟩

end Block297
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block297.block297V
#check Erdos1038Lean.M1817475.Block297.block297_left_V_pos
#check Erdos1038Lean.M1817475.Block297.block297_right_V_pos
#check Erdos1038Lean.M1817475.Block297.block297_reallog_certificate_proof
