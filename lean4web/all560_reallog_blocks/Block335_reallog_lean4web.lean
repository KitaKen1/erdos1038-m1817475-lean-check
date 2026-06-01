/-
Self-contained Lean4Web paste file.
Block 335 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block335

def block335LeftL : Rat := ((2349343750000000009 : Rat) / 3125000000000000000)
def block335LeftR : Rat := ((7519854910714285743 : Rat) / 10000000000000000000)
def block335RightL : Rat := ((5474343750000000009 : Rat) / 3125000000000000000)
def block335RightR : Rat := ((27519854910714285743 : Rat) / 10000000000000000000)

def block335LeftBoxes : List RatBox := [
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2349343750000000009 : Rat) / 3125000000000000000), R := ((7519854910714285743 : Rat) / 10000000000000000000), D0 := ((7519854910714285743 : Rat) / 10000000000000000000), D1 := ((3330265937499999991 : Rat) / 3125000000000000000), D2 := ((5644203124999999991 : Rat) / 3125000000000000000), D3 := ((95995106339285714149 : Rat) / 50000000000000000000), D4 := ((50514503214285711727 : Rat) / 25000000000000000000), LB := ((1613708546740547 : Rat) / 250000000000000000) }
]

def block335LeftCertificate : Bool :=
  allBoxesValid block335LeftBoxes &&
  coversFromBool block335LeftBoxes block335LeftL block335LeftR

theorem block335LeftCertificate_eq_true :
    block335LeftCertificate = true := by
  native_decide

def block335RightChunk000 : List RatBox := [
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((5474343750000000009 : Rat) / 3125000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((205265937499999991 : Rat) / 3125000000000000000), D2 := ((2519203124999999991 : Rat) / 3125000000000000000), D3 := ((45995106339285714149 : Rat) / 50000000000000000000), D4 := ((25514503214285711727 : Rat) / 25000000000000000000), LB := ((4944697613965457 : Rat) / 2500000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42710851339285714293 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((4829269957993209 : Rat) / 25000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24199353839285714293 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((12458900147766519 : Rat) / 100000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19571479464285714293 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((1660065926273847 : Rat) / 20000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17257542276785714293 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((11008233979746297 : Rat) / 500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14943605089285714293 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((4084024638700151 : Rat) / 200000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13786636495535714293 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((629378848264861 : Rat) / 4000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12629667901785714293 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((6187296989718621 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((12051183604910714293 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((2616508097208807 : Rat) / 250000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11761941456473214293 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((7421690820267973 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11472699308035714293 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((1174765793596641 : Rat) / 250000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11183457159598214293 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((1156792375406543 : Rat) / 500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10894215011160714293 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((28294915753979133 : Rat) / 100000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10604972862723214293 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((80025454724853 : Rat) / 20000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10460351788504464293 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((1650734166565429 : Rat) / 500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10315730714285714293 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((27048259866028213 : Rat) / 10000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10171109640066964293 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((17719553873351 : Rat) / 8000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((10026488565848214293 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((3671470933963139 : Rat) / 2000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9881867491629464293 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((7857324677072869 : Rat) / 5000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9737246417410714293 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((445873868408107 : Rat) / 312500000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9592625343191964293 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((87927856609573 : Rat) / 62500000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9448004268973214293 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((15172445232612963 : Rat) / 10000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9303383194754464293 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((4410539527005819 : Rat) / 2500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9158762120535714293 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((430932936207673 : Rat) / 200000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((9014141046316964293 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((2696288049325063 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8869519972098214293 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((3397708217036721 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8724898897879464293 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((853727400306803 : Rat) / 200000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8580277823660714293 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((2661444806701177 : Rat) / 12500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8291035675223214293 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((7362725837318021 : Rat) / 2500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((8001793526785714293 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((6576340010858411 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7712551378348214293 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((11278794106707013 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7423309229910714293 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1853531177136207 : Rat) / 250000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6844824933035714293 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((1493045539134763 : Rat) / 250000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028861856339285714293 : Rat) / 400000000000000000000), D0 := ((1028861856339285714293 : Rat) / 400000000000000000000), D1 := ((301871816339285714293 : Rat) / 400000000000000000000), D2 := ((5687856339285714293 : Rat) / 400000000000000000000), D3 := ((5687856339285714293 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((4646018869282473 : Rat) / 100000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028861856339285714293 : Rat) / 400000000000000000000), R := ((517274856339285714293 : Rat) / 200000000000000000000), D0 := ((517274856339285714293 : Rat) / 200000000000000000000), D1 := ((153779836339285714293 : Rat) / 200000000000000000000), D2 := ((5687856339285714293 : Rat) / 200000000000000000000), D3 := ((39814994375000000051 : Rat) / 400000000000000000000), D4 := ((80086195089285674491 : Rat) / 400000000000000000000), LB := ((484203150018233 : Rat) / 25000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517274856339285714293 : Rat) / 200000000000000000000), R := ((1040237569017857142879 : Rat) / 400000000000000000000), D0 := ((1040237569017857142879 : Rat) / 400000000000000000000), D1 := ((313247529017857142879 : Rat) / 400000000000000000000), D2 := ((17063569017857142879 : Rat) / 400000000000000000000), D3 := ((17063569017857142879 : Rat) / 200000000000000000000), D4 := ((37199169374999980099 : Rat) / 200000000000000000000), LB := ((4956990043743309 : Rat) / 500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1040237569017857142879 : Rat) / 400000000000000000000), R := ((261481356339285714293 : Rat) / 100000000000000000000), D0 := ((261481356339285714293 : Rat) / 100000000000000000000), D1 := ((79733846339285714293 : Rat) / 100000000000000000000), D2 := ((5687856339285714293 : Rat) / 100000000000000000000), D3 := ((5687856339285714293 : Rat) / 80000000000000000000), D4 := ((13742096482142849181 : Rat) / 80000000000000000000), LB := ((43952358781999 : Rat) / 3906250000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261481356339285714293 : Rat) / 100000000000000000000), R := ((210322656339285714293 : Rat) / 80000000000000000000), D0 := ((210322656339285714293 : Rat) / 80000000000000000000), D1 := ((64924648339285714293 : Rat) / 80000000000000000000), D2 := ((5687856339285714293 : Rat) / 80000000000000000000), D3 := ((5687856339285714293 : Rat) / 100000000000000000000), D4 := ((15755656517857132903 : Rat) / 100000000000000000000), LB := ((2282077795343007 : Rat) / 100000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((210322656339285714293 : Rat) / 80000000000000000000), R := ((528650569017857142879 : Rat) / 200000000000000000000), D0 := ((528650569017857142879 : Rat) / 200000000000000000000), D1 := ((165155549017857142879 : Rat) / 200000000000000000000), D2 := ((17063569017857142879 : Rat) / 200000000000000000000), D3 := ((17063569017857142879 : Rat) / 400000000000000000000), D4 := ((57334769732142817319 : Rat) / 400000000000000000000), LB := ((588726522747509 : Rat) / 12500000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528650569017857142879 : Rat) / 200000000000000000000), R := ((133584606339285714293 : Rat) / 50000000000000000000), D0 := ((133584606339285714293 : Rat) / 50000000000000000000), D1 := ((42710851339285714293 : Rat) / 50000000000000000000), D2 := ((5687856339285714293 : Rat) / 50000000000000000000), D3 := ((5687856339285714293 : Rat) / 200000000000000000000), D4 := ((25823456696428551513 : Rat) / 200000000000000000000), LB := ((3200123171268607 : Rat) / 50000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133584606339285714293 : Rat) / 50000000000000000000), R := ((269176546785714285797 : Rat) / 100000000000000000000), D0 := ((269176546785714285797 : Rat) / 100000000000000000000), D1 := ((87429036785714285797 : Rat) / 100000000000000000000), D2 := ((13383046785714285797 : Rat) / 100000000000000000000), D3 := ((2007334107142857211 : Rat) / 100000000000000000000), D4 := ((1006780017857141861 : Rat) / 10000000000000000000), LB := ((11157189584294097 : Rat) / 100000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((269176546785714285797 : Rat) / 100000000000000000000), R := ((8474496277901785719 : Rat) / 3125000000000000000), D0 := ((8474496277901785719 : Rat) / 3125000000000000000), D1 := ((2794886590401785719 : Rat) / 3125000000000000000), D2 := ((480949402901785719 : Rat) / 3125000000000000000), D3 := ((2007334107142857211 : Rat) / 50000000000000000000), D4 := ((8060466071428561399 : Rat) / 100000000000000000000), LB := ((3229222539244403 : Rat) / 500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8474496277901785719 : Rat) / 3125000000000000000), R := ((1086742857678571429243 : Rat) / 400000000000000000000), D0 := ((1086742857678571429243 : Rat) / 400000000000000000000), D1 := ((359752817678571429243 : Rat) / 400000000000000000000), D2 := ((63568857678571429243 : Rat) / 400000000000000000000), D3 := ((18066006964285714899 : Rat) / 400000000000000000000), D4 := ((1513282991071426047 : Rat) / 25000000000000000000), LB := ((10051421551160483 : Rat) / 500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1086742857678571429243 : Rat) / 400000000000000000000), R := ((544375095892857143227 : Rat) / 200000000000000000000), D0 := ((544375095892857143227 : Rat) / 200000000000000000000), D1 := ((180880075892857143227 : Rat) / 200000000000000000000), D2 := ((32788095892857143227 : Rat) / 200000000000000000000), D3 := ((2007334107142857211 : Rat) / 40000000000000000000), D4 := ((22205193749999959541 : Rat) / 400000000000000000000), LB := ((8197477309626167 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((544375095892857143227 : Rat) / 200000000000000000000), R := ((2179507717678571430119 : Rat) / 800000000000000000000), D0 := ((2179507717678571430119 : Rat) / 800000000000000000000), D1 := ((725527637678571430119 : Rat) / 800000000000000000000), D2 := ((133159717678571430119 : Rat) / 800000000000000000000), D3 := ((42154016250000001431 : Rat) / 800000000000000000000), D4 := ((2019785964285710233 : Rat) / 40000000000000000000), LB := ((77352432300371 : Rat) / 7812500000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2179507717678571430119 : Rat) / 800000000000000000000), R := ((218151505178571428733 : Rat) / 80000000000000000000), D0 := ((218151505178571428733 : Rat) / 80000000000000000000), D1 := ((72753497178571428733 : Rat) / 80000000000000000000), D2 := ((13516705178571428733 : Rat) / 80000000000000000000), D3 := ((22080675178571429321 : Rat) / 400000000000000000000), D4 := ((38388385178571347449 : Rat) / 800000000000000000000), LB := ((1485919565063859 : Rat) / 250000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((218151505178571428733 : Rat) / 80000000000000000000), R := ((2183522385892857144541 : Rat) / 800000000000000000000), D0 := ((2183522385892857144541 : Rat) / 800000000000000000000), D1 := ((729542305892857144541 : Rat) / 800000000000000000000), D2 := ((137174385892857144541 : Rat) / 800000000000000000000), D3 := ((46168684464285715853 : Rat) / 800000000000000000000), D4 := ((18190525535714245119 : Rat) / 400000000000000000000), LB := ((3349565466127663 : Rat) / 1250000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2183522385892857144541 : Rat) / 800000000000000000000), R := ((273191215000000000219 : Rat) / 100000000000000000000), D0 := ((273191215000000000219 : Rat) / 100000000000000000000), D1 := ((91443705000000000219 : Rat) / 100000000000000000000), D2 := ((17397715000000000219 : Rat) / 100000000000000000000), D3 := ((6022002321428571633 : Rat) / 100000000000000000000), D4 := ((34373716964285633027 : Rat) / 800000000000000000000), LB := ((1258849144518681 : Rat) / 10000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((273191215000000000219 : Rat) / 100000000000000000000), R := ((874613354821428572143 : Rat) / 320000000000000000000), D0 := ((874613354821428572143 : Rat) / 320000000000000000000), D1 := ((293021322821428572143 : Rat) / 320000000000000000000), D2 := ((56074154821428572143 : Rat) / 320000000000000000000), D3 := ((98359371250000003339 : Rat) / 1600000000000000000000), D4 := ((4045797857142846977 : Rat) / 100000000000000000000), LB := ((8286304908123321 : Rat) / 2500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((874613354821428572143 : Rat) / 320000000000000000000), R := ((2187537054107142858963 : Rat) / 800000000000000000000), D0 := ((2187537054107142858963 : Rat) / 800000000000000000000), D1 := ((733556974107142858963 : Rat) / 800000000000000000000), D2 := ((141189054107142858963 : Rat) / 800000000000000000000), D3 := ((2007334107142857211 : Rat) / 32000000000000000000), D4 := ((62725431607142694421 : Rat) / 1600000000000000000000), LB := ((2633078665592703 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2187537054107142858963 : Rat) / 800000000000000000000), R := ((4377081442321428575137 : Rat) / 1600000000000000000000), D0 := ((4377081442321428575137 : Rat) / 1600000000000000000000), D1 := ((1469121282321428575137 : Rat) / 1600000000000000000000), D2 := ((284385442321428575137 : Rat) / 1600000000000000000000), D3 := ((102374039464285717761 : Rat) / 1600000000000000000000), D4 := ((6071809749999983721 : Rat) / 160000000000000000000), LB := ((1077247234356149 : Rat) / 500000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4377081442321428575137 : Rat) / 1600000000000000000000), R := ((1094772194107142858087 : Rat) / 400000000000000000000), D0 := ((1094772194107142858087 : Rat) / 400000000000000000000), D1 := ((367782154107142858087 : Rat) / 400000000000000000000), D2 := ((71598194107142858087 : Rat) / 400000000000000000000), D3 := ((26095343392857143743 : Rat) / 400000000000000000000), D4 := ((58710763392856979999 : Rat) / 1600000000000000000000), LB := ((1885939216324961 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094772194107142858087 : Rat) / 400000000000000000000), R := ((4381096110535714289559 : Rat) / 1600000000000000000000), D0 := ((4381096110535714289559 : Rat) / 1600000000000000000000), D1 := ((1473135950535714289559 : Rat) / 1600000000000000000000), D2 := ((288400110535714289559 : Rat) / 1600000000000000000000), D3 := ((106388707678571432183 : Rat) / 1600000000000000000000), D4 := ((14175857321428530697 : Rat) / 400000000000000000000), LB := ((9178495823361499 : Rat) / 5000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4381096110535714289559 : Rat) / 1600000000000000000000), R := ((438310344464285714677 : Rat) / 160000000000000000000), D0 := ((438310344464285714677 : Rat) / 160000000000000000000), D1 := ((147514328464285714677 : Rat) / 160000000000000000000), D2 := ((29040744464285714677 : Rat) / 160000000000000000000), D3 := ((54198020892857144697 : Rat) / 800000000000000000000), D4 := ((54696095178571265577 : Rat) / 1600000000000000000000), LB := ((2013309737672553 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((438310344464285714677 : Rat) / 160000000000000000000), R := ((4385110778750000003981 : Rat) / 1600000000000000000000), D0 := ((4385110778750000003981 : Rat) / 1600000000000000000000), D1 := ((1477150618750000003981 : Rat) / 1600000000000000000000), D2 := ((292414778750000003981 : Rat) / 1600000000000000000000), D3 := ((22080675178571429321 : Rat) / 320000000000000000000), D4 := ((26344380535714204183 : Rat) / 800000000000000000000), LB := ((2429715796297971 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4385110778750000003981 : Rat) / 1600000000000000000000), R := ((548389764107142857649 : Rat) / 200000000000000000000), D0 := ((548389764107142857649 : Rat) / 200000000000000000000), D1 := ((184894744107142857649 : Rat) / 200000000000000000000), D2 := ((36802764107142857649 : Rat) / 200000000000000000000), D3 := ((14051338750000000477 : Rat) / 200000000000000000000), D4 := ((10136285392857110231 : Rat) / 320000000000000000000), LB := ((30974655372751903 : Rat) / 10000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((548389764107142857649 : Rat) / 200000000000000000000), R := ((4389125446964285718403 : Rat) / 1600000000000000000000), D0 := ((4389125446964285718403 : Rat) / 1600000000000000000000), D1 := ((1481165286964285718403 : Rat) / 1600000000000000000000), D2 := ((296429446964285718403 : Rat) / 1600000000000000000000), D3 := ((114418044107142861027 : Rat) / 1600000000000000000000), D4 := ((6084261607142836743 : Rat) / 200000000000000000000), LB := ((806189181144179 : Rat) / 200000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4389125446964285718403 : Rat) / 1600000000000000000000), R := ((2195566390535714287807 : Rat) / 800000000000000000000), D0 := ((2195566390535714287807 : Rat) / 800000000000000000000), D1 := ((741586310535714287807 : Rat) / 800000000000000000000), D2 := ((149218390535714287807 : Rat) / 800000000000000000000), D3 := ((58212689107142859119 : Rat) / 800000000000000000000), D4 := ((46666758749999836733 : Rat) / 1600000000000000000000), LB := ((10493339533077961 : Rat) / 2000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2195566390535714287807 : Rat) / 800000000000000000000), R := ((1098786862321428572509 : Rat) / 400000000000000000000), D0 := ((1098786862321428572509 : Rat) / 400000000000000000000), D1 := ((371796822321428572509 : Rat) / 400000000000000000000), D2 := ((75612862321428572509 : Rat) / 400000000000000000000), D3 := ((6022002321428571633 : Rat) / 80000000000000000000), D4 := ((22329712321428489761 : Rat) / 800000000000000000000), LB := ((2292368583326043 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1098786862321428572509 : Rat) / 400000000000000000000), R := ((2199581058750000002229 : Rat) / 800000000000000000000), D0 := ((2199581058750000002229 : Rat) / 800000000000000000000), D1 := ((745600978750000002229 : Rat) / 800000000000000000000), D2 := ((153233058750000002229 : Rat) / 800000000000000000000), D3 := ((62227357321428573541 : Rat) / 800000000000000000000), D4 := ((406447564285712651 : Rat) / 16000000000000000000), LB := ((6408116927041907 : Rat) / 1000000000000000000) },
  { w1 := ((9386554495149547 : Rat) / 10000000000000000), w2 := ((2365544121424913 : Rat) / 50000000000000000), w3 := ((1808451117390093 : Rat) / 12500000000000000), w4 := ((1372360314347817 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133584606339285714293 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2199581058750000002229 : Rat) / 800000000000000000000), R := ((27519854910714285743 : Rat) / 10000000000000000000), D0 := ((27519854910714285743 : Rat) / 10000000000000000000), D1 := ((9345103910714285743 : Rat) / 10000000000000000000), D2 := ((1940504910714285743 : Rat) / 10000000000000000000), D3 := ((2007334107142857211 : Rat) / 25000000000000000000), D4 := ((18315044107142775339 : Rat) / 800000000000000000000), LB := ((3008936660837791 : Rat) / 250000000000000000) }
]

def block335RightChunk000L : Rat := ((5474343750000000009 : Rat) / 3125000000000000000)
def block335RightChunk000R : Rat := ((27519854910714285743 : Rat) / 10000000000000000000)

def block335RightChunk000Certificate : Bool :=
  allBoxesValid block335RightChunk000 &&
  coversFromBool block335RightChunk000 block335RightChunk000L block335RightChunk000R

theorem block335RightChunk000Certificate_eq_true :
    block335RightChunk000Certificate = true := by
  native_decide

def block335RightChainCertificate : Bool :=
  decide (
    block335RightL = ((5474343750000000009 : Rat) / 3125000000000000000) /\
    ((27519854910714285743 : Rat) / 10000000000000000000) = block335RightR)

theorem block335RightChainCertificate_eq_true :
    block335RightChainCertificate = true := by
  native_decide

def block335LeftBoxCount : Nat := boxCount block335LeftBoxes
def block335RightBoxCount : Nat := 61

def block335_rational_certificate : Prop :=
    block335LeftCertificate = true /\
    block335RightChainCertificate = true /\
    block335RightChunk000Certificate = true

theorem block335_rational_certificate_proof :
    block335_rational_certificate := by
  exact ⟨block335LeftCertificate_eq_true, block335RightChainCertificate_eq_true, block335RightChunk000Certificate_eq_true⟩

end Block335
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block335

open Set

def block335W1 : Rat := ((9386554495149547 : Rat) / 10000000000000000)
def block335W2 : Rat := ((2365544121424913 : Rat) / 50000000000000000)
def block335W3 : Rat := ((1808451117390093 : Rat) / 12500000000000000)
def block335W4 : Rat := ((1372360314347817 : Rat) / 10000000000000000)
def block335S1 : Rat := ((18174751 : Rat) / 10000000)
def block335S2 : Rat := ((511587 : Rat) / 200000)
def block335S3 : Rat := ((133584606339285714293 : Rat) / 50000000000000000000)
def block335S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block335V (y : ℝ) : ℝ :=
  ratPotential block335W1 block335W2 block335W3 block335W4 block335S1 block335S2 block335S3 block335S4 y

def block335LeftParamsCertificate : Bool :=
  allBoxesSameParams block335LeftBoxes block335W1 block335W2 block335W3 block335W4 block335S1 block335S2 block335S3 block335S4

theorem block335LeftParamsCertificate_eq_true :
    block335LeftParamsCertificate = true := by
  native_decide

theorem block335_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block335LeftL : ℝ) (block335LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block335S1 : ℝ))
    (hy2ne : y ≠ (block335S2 : ℝ))
    (hy3ne : y ≠ (block335S3 : ℝ))
    (hy4ne : y ≠ (block335S4 : ℝ)) :
    0 < block335V y := by
  have hcert := block335LeftCertificate_eq_true
  unfold block335LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block335LeftBoxes) (lo := block335LeftL) (hi := block335LeftR)
    (w1 := block335W1) (w2 := block335W2) (w3 := block335W3) (w4 := block335W4)
    (s1 := block335S1) (s2 := block335S2) (s3 := block335S3) (s4 := block335S4)
    hboxes hcover block335LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block335RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block335RightChunk000 block335W1 block335W2 block335W3 block335W4 block335S1 block335S2 block335S3 block335S4

theorem block335RightChunk000ParamsCertificate_eq_true :
    block335RightChunk000ParamsCertificate = true := by
  native_decide

theorem block335_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block335RightChunk000L : ℝ) (block335RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block335S1 : ℝ))
    (hy2ne : y ≠ (block335S2 : ℝ))
    (hy3ne : y ≠ (block335S3 : ℝ))
    (hy4ne : y ≠ (block335S4 : ℝ)) :
    0 < block335V y := by
  have hcert := block335RightChunk000Certificate_eq_true
  unfold block335RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block335RightChunk000) (lo := block335RightChunk000L) (hi := block335RightChunk000R)
    (w1 := block335W1) (w2 := block335W2) (w3 := block335W3) (w4 := block335W4)
    (s1 := block335S1) (s2 := block335S2) (s3 := block335S3) (s4 := block335S4)
    hboxes hcover block335RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block335_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block335RightL : ℝ) (block335RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block335S1 : ℝ))
    (hy2ne : y ≠ (block335S2 : ℝ))
    (hy3ne : y ≠ (block335S3 : ℝ))
    (hy4ne : y ≠ (block335S4 : ℝ)) :
    0 < block335V y := by
  have hL : (block335RightChunk000L : ℝ) = (block335RightL : ℝ) := by
    norm_num [block335RightChunk000L, block335RightL]
  have hR : (block335RightChunk000R : ℝ) = (block335RightR : ℝ) := by
    norm_num [block335RightChunk000R, block335RightR]
  have hyc : y ∈ Icc (block335RightChunk000L : ℝ) (block335RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block335_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block335_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block335LeftL : ℝ) (block335LeftR : ℝ) →
    y ≠ 0 → y ≠ (block335S1 : ℝ) → y ≠ (block335S2 : ℝ) →
    y ≠ (block335S3 : ℝ) → y ≠ (block335S4 : ℝ) → 0 < block335V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block335RightL : ℝ) (block335RightR : ℝ) →
    y ≠ 0 → y ≠ (block335S1 : ℝ) → y ≠ (block335S2 : ℝ) →
    y ≠ (block335S3 : ℝ) → y ≠ (block335S4 : ℝ) → 0 < block335V y)

theorem block335_reallog_certificate_proof :
    block335_reallog_certificate := by
  exact ⟨block335_left_V_pos, block335_right_V_pos⟩

end Block335
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block335.block335V
#check Erdos1038Lean.M1817475.Block335.block335_left_V_pos
#check Erdos1038Lean.M1817475.Block335.block335_right_V_pos
#check Erdos1038Lean.M1817475.Block335.block335_reallog_certificate_proof
