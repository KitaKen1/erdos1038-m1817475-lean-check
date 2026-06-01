/-
Self-contained Lean4Web paste file.
Block 11 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block011

def block011LeftL : Rat := ((10189113839285714287 : Rat) / 12500000000000000000)
def block011LeftR : Rat := ((40766229910714285719 : Rat) / 50000000000000000000)
def block011RightL : Rat := ((22689113839285714287 : Rat) / 12500000000000000000)
def block011RightR : Rat := ((140766229910714285719 : Rat) / 50000000000000000000)

def block011LeftBoxes : List RatBox := [
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((10189113839285714287 : Rat) / 12500000000000000000), R := ((40766229910714285719 : Rat) / 50000000000000000000), D0 := ((40766229910714285719 : Rat) / 50000000000000000000), D1 := ((12529324910714285713 : Rat) / 12500000000000000000), D2 := ((21785073660714285713 : Rat) / 12500000000000000000), D3 := ((23248579598214285713 : Rat) / 12500000000000000000), D4 := ((25203491562499998723 : Rat) / 12500000000000000000), LB := ((1220542735438937 : Rat) / 250000000000000000) }
]

def block011LeftCertificate : Bool :=
  allBoxesValid block011LeftBoxes &&
  coversFromBool block011LeftBoxes block011LeftL block011LeftR

theorem block011LeftCertificate_eq_true :
    block011LeftCertificate = true := by
  native_decide

def block011RightChunk000 : List RatBox := [
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((22689113839285714287 : Rat) / 12500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((29324910714285713 : Rat) / 12500000000000000000), D2 := ((9285073660714285713 : Rat) / 12500000000000000000), D3 := ((10748579598214285713 : Rat) / 12500000000000000000), D4 := ((12703491562499998723 : Rat) / 12500000000000000000), LB := ((543959998034531 : Rat) / 10000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((1267416665178571301 : Rat) / 1250000000000000000), LB := ((919677138582119 : Rat) / 500000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((511587 : Rat) / 200000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((341841790178571301 : Rat) / 1250000000000000000), LB := ((7673209791889337 : Rat) / 10000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((274517003660714285719 : Rat) / 100000000000000000000), D0 := ((274517003660714285719 : Rat) / 100000000000000000000), D1 := ((92769493660714285719 : Rat) / 100000000000000000000), D2 := ((18723503660714285719 : Rat) / 100000000000000000000), D3 := ((7015456160714285719 : Rat) / 100000000000000000000), D4 := ((195491196428571301 : Rat) / 1250000000000000000), LB := ((1936372644346121 : Rat) / 12500000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((274517003660714285719 : Rat) / 100000000000000000000), R := ((221016694160714285719 : Rat) / 80000000000000000000), D0 := ((221016694160714285719 : Rat) / 80000000000000000000), D1 := ((75618686160714285719 : Rat) / 80000000000000000000), D2 := ((16381894160714285719 : Rat) / 80000000000000000000), D3 := ((7015456160714285719 : Rat) / 80000000000000000000), D4 := ((8623839553571418361 : Rat) / 100000000000000000000), LB := ((2517673668453937 : Rat) / 20000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((221016694160714285719 : Rat) / 80000000000000000000), R := ((556049463482142857157 : Rat) / 200000000000000000000), D0 := ((556049463482142857157 : Rat) / 200000000000000000000), D1 := ((192554443482142857157 : Rat) / 200000000000000000000), D2 := ((44462463482142857157 : Rat) / 200000000000000000000), D3 := ((21046368482142857157 : Rat) / 200000000000000000000), D4 := ((1099196082142855509 : Rat) / 16000000000000000000), LB := ((3459607973553269 : Rat) / 500000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((556049463482142857157 : Rat) / 200000000000000000000), R := ((178216446560714285719 : Rat) / 64000000000000000000), D0 := ((178216446560714285719 : Rat) / 64000000000000000000), D1 := ((61898040160714285719 : Rat) / 64000000000000000000), D2 := ((14508606560714285719 : Rat) / 64000000000000000000), D3 := ((7015456160714285719 : Rat) / 64000000000000000000), D4 := ((10232222946428551003 : Rat) / 200000000000000000000), LB := ((758452800017777 : Rat) / 20000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((178216446560714285719 : Rat) / 64000000000000000000), R := ((2231213310089285714347 : Rat) / 800000000000000000000), D0 := ((2231213310089285714347 : Rat) / 800000000000000000000), D1 := ((777233230089285714347 : Rat) / 800000000000000000000), D2 := ((184865310089285714347 : Rat) / 800000000000000000000), D3 := ((91200930089285714347 : Rat) / 800000000000000000000), D4 := ((14968465482142824461 : Rat) / 320000000000000000000), LB := ((8580400036971081 : Rat) / 500000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2231213310089285714347 : Rat) / 800000000000000000000), R := ((8931868696517857143107 : Rat) / 3200000000000000000000), D0 := ((8931868696517857143107 : Rat) / 3200000000000000000000), D1 := ((3115948376517857143107 : Rat) / 3200000000000000000000), D2 := ((746476696517857143107 : Rat) / 3200000000000000000000), D3 := ((371819176517857143107 : Rat) / 3200000000000000000000), D4 := ((33913435624999918293 : Rat) / 800000000000000000000), LB := ((5108039189174851 : Rat) / 250000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8931868696517857143107 : Rat) / 3200000000000000000000), R := ((4469442076339285714413 : Rat) / 1600000000000000000000), D0 := ((4469442076339285714413 : Rat) / 1600000000000000000000), D1 := ((1561481916339285714413 : Rat) / 1600000000000000000000), D2 := ((376746076339285714413 : Rat) / 1600000000000000000000), D3 := ((189417316339285714413 : Rat) / 1600000000000000000000), D4 := ((128638286339285387453 : Rat) / 3200000000000000000000), LB := ((3068204479734299 : Rat) / 250000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4469442076339285714413 : Rat) / 1600000000000000000000), R := ((1789179921767857142909 : Rat) / 640000000000000000000), D0 := ((1789179921767857142909 : Rat) / 640000000000000000000), D1 := ((625995857767857142909 : Rat) / 640000000000000000000), D2 := ((152101521767857142909 : Rat) / 640000000000000000000), D3 := ((77170017767857142909 : Rat) / 640000000000000000000), D4 := ((60811415089285550867 : Rat) / 1600000000000000000000), LB := ((4915153936381311 : Rat) / 1000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1789179921767857142909 : Rat) / 640000000000000000000), R := ((17898814673839285714809 : Rat) / 6400000000000000000000), D0 := ((17898814673839285714809 : Rat) / 6400000000000000000000), D1 := ((6266974033839285714809 : Rat) / 6400000000000000000000), D2 := ((1528030673839285714809 : Rat) / 6400000000000000000000), D3 := ((778715633839285714809 : Rat) / 6400000000000000000000), D4 := ((22921474803571363203 : Rat) / 640000000000000000000), LB := ((1149886626161653 : Rat) / 125000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17898814673839285714809 : Rat) / 6400000000000000000000), R := ((1119114383125000000033 : Rat) / 400000000000000000000), D0 := ((1119114383125000000033 : Rat) / 400000000000000000000), D1 := ((392124343125000000033 : Rat) / 400000000000000000000), D2 := ((95940383125000000033 : Rat) / 400000000000000000000), D3 := ((49108193125000000033 : Rat) / 400000000000000000000), D4 := ((222199291874999346311 : Rat) / 6400000000000000000000), LB := ((126415619149709 : Rat) / 20000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1119114383125000000033 : Rat) / 400000000000000000000), R := ((17912845586160714286247 : Rat) / 6400000000000000000000), D0 := ((17912845586160714286247 : Rat) / 6400000000000000000000), D1 := ((6281004946160714286247 : Rat) / 6400000000000000000000), D2 := ((1542061586160714286247 : Rat) / 6400000000000000000000), D3 := ((792746546160714286247 : Rat) / 6400000000000000000000), D4 := ((13448989732142816287 : Rat) / 400000000000000000000), LB := ((37067736349610803 : Rat) / 10000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17912845586160714286247 : Rat) / 6400000000000000000000), R := ((8959930521160714285983 : Rat) / 3200000000000000000000), D0 := ((8959930521160714285983 : Rat) / 3200000000000000000000), D1 := ((3144010201160714285983 : Rat) / 3200000000000000000000), D2 := ((774538521160714285983 : Rat) / 3200000000000000000000), D3 := ((399881001160714285983 : Rat) / 3200000000000000000000), D4 := ((208168379553570774873 : Rat) / 6400000000000000000000), LB := ((13737914083876701 : Rat) / 10000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8959930521160714285983 : Rat) / 3200000000000000000000), R := ((35846737540803571429651 : Rat) / 12800000000000000000000), D0 := ((35846737540803571429651 : Rat) / 12800000000000000000000), D1 := ((12583056260803571429651 : Rat) / 12800000000000000000000), D2 := ((3105169540803571429651 : Rat) / 12800000000000000000000), D3 := ((1606539460803571429651 : Rat) / 12800000000000000000000), D4 := ((100576461696428244577 : Rat) / 3200000000000000000000), LB := ((2348245724084319 : Rat) / 500000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35846737540803571429651 : Rat) / 12800000000000000000000), R := ((3585375299696428571537 : Rat) / 1280000000000000000000), D0 := ((3585375299696428571537 : Rat) / 1280000000000000000000), D1 := ((1259007171696428571537 : Rat) / 1280000000000000000000), D2 := ((311218499696428571537 : Rat) / 1280000000000000000000), D3 := ((161355491696428571537 : Rat) / 1280000000000000000000), D4 := ((395290390624998692589 : Rat) / 12800000000000000000000), LB := ((37954159922214403 : Rat) / 10000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3585375299696428571537 : Rat) / 1280000000000000000000), R := ((35860768453125000001089 : Rat) / 12800000000000000000000), D0 := ((35860768453125000001089 : Rat) / 12800000000000000000000), D1 := ((12597087173125000001089 : Rat) / 12800000000000000000000), D2 := ((3119200453125000001089 : Rat) / 12800000000000000000000), D3 := ((1620570373125000001089 : Rat) / 12800000000000000000000), D4 := ((38827493446428440687 : Rat) / 1280000000000000000000), LB := ((1190813490448539 : Rat) / 400000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35860768453125000001089 : Rat) / 12800000000000000000000), R := ((4483472988660714285851 : Rat) / 1600000000000000000000), D0 := ((4483472988660714285851 : Rat) / 1600000000000000000000), D1 := ((1575512828660714285851 : Rat) / 1600000000000000000000), D2 := ((390776988660714285851 : Rat) / 1600000000000000000000), D3 := ((203448228660714285851 : Rat) / 1600000000000000000000), D4 := ((381259478303570121151 : Rat) / 12800000000000000000000), LB := ((2739564120053 : Rat) / 1220703125000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4483472988660714285851 : Rat) / 1600000000000000000000), R := ((35874799365446428572527 : Rat) / 12800000000000000000000), D0 := ((35874799365446428572527 : Rat) / 12800000000000000000000), D1 := ((12611118085446428572527 : Rat) / 12800000000000000000000), D2 := ((3133231365446428572527 : Rat) / 12800000000000000000000), D3 := ((1634601285446428572527 : Rat) / 12800000000000000000000), D4 := ((46780502767856979429 : Rat) / 1600000000000000000000), LB := ((16001359958388583 : Rat) / 10000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35874799365446428572527 : Rat) / 12800000000000000000000), R := ((17940907410803571429123 : Rat) / 6400000000000000000000), D0 := ((17940907410803571429123 : Rat) / 6400000000000000000000), D1 := ((6309066770803571429123 : Rat) / 6400000000000000000000), D2 := ((1570123410803571429123 : Rat) / 6400000000000000000000), D3 := ((820808370803571429123 : Rat) / 6400000000000000000000), D4 := ((367228565982141549713 : Rat) / 12800000000000000000000), LB := ((1047931727946927 : Rat) / 1000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17940907410803571429123 : Rat) / 6400000000000000000000), R := ((7177766055553571428793 : Rat) / 2560000000000000000000), D0 := ((7177766055553571428793 : Rat) / 2560000000000000000000), D1 := ((2525029799553571428793 : Rat) / 2560000000000000000000), D2 := ((629452455553571428793 : Rat) / 2560000000000000000000), D3 := ((329726439553571428793 : Rat) / 2560000000000000000000), D4 := ((180106554910713631997 : Rat) / 6400000000000000000000), LB := ((1477671924503543 : Rat) / 2500000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((7177766055553571428793 : Rat) / 2560000000000000000000), R := ((8973961433482142857421 : Rat) / 3200000000000000000000), D0 := ((8973961433482142857421 : Rat) / 3200000000000000000000), D1 := ((3158041113482142857421 : Rat) / 3200000000000000000000), D2 := ((788569433482142857421 : Rat) / 3200000000000000000000), D3 := ((413911913482142857421 : Rat) / 3200000000000000000000), D4 := ((14127906146428519131 : Rat) / 512000000000000000000), LB := ((23318039657849177 : Rat) / 100000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8973961433482142857421 : Rat) / 3200000000000000000000), R := ((71798706924017857145087 : Rat) / 25600000000000000000000), D0 := ((71798706924017857145087 : Rat) / 25600000000000000000000), D1 := ((25271344364017857145087 : Rat) / 25600000000000000000000), D2 := ((6315570924017857145087 : Rat) / 25600000000000000000000), D3 := ((3318310764017857145087 : Rat) / 25600000000000000000000), D4 := ((86545549374999673139 : Rat) / 3200000000000000000000), LB := ((2645702258231797 : Rat) / 1000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71798706924017857145087 : Rat) / 25600000000000000000000), R := ((35902861190089285715403 : Rat) / 12800000000000000000000), D0 := ((35902861190089285715403 : Rat) / 12800000000000000000000), D1 := ((12639179910089285715403 : Rat) / 12800000000000000000000), D2 := ((3161293190089285715403 : Rat) / 12800000000000000000000), D3 := ((1662663110089285715403 : Rat) / 12800000000000000000000), D4 := ((685348938839283099393 : Rat) / 25600000000000000000000), LB := ((25572768447441607 : Rat) / 10000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35902861190089285715403 : Rat) / 12800000000000000000000), R := ((2872509513453571428661 : Rat) / 1024000000000000000000), D0 := ((2872509513453571428661 : Rat) / 1024000000000000000000), D1 := ((1011415011053571428661 : Rat) / 1024000000000000000000), D2 := ((253184073453571428661 : Rat) / 1024000000000000000000), D3 := ((133293667053571428661 : Rat) / 1024000000000000000000), D4 := ((339166741339284406837 : Rat) / 12800000000000000000000), LB := ((24961114387398453 : Rat) / 10000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2872509513453571428661 : Rat) / 1024000000000000000000), R := ((17954938323125000000561 : Rat) / 6400000000000000000000), D0 := ((17954938323125000000561 : Rat) / 6400000000000000000000), D1 := ((6323097683125000000561 : Rat) / 6400000000000000000000), D2 := ((1584154323125000000561 : Rat) / 6400000000000000000000), D3 := ((834839283125000000561 : Rat) / 6400000000000000000000), D4 := ((134263605303570905591 : Rat) / 5120000000000000000000), LB := ((3078446764077647 : Rat) / 1250000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17954938323125000000561 : Rat) / 6400000000000000000000), R := ((71826768748660714287963 : Rat) / 25600000000000000000000), D0 := ((71826768748660714287963 : Rat) / 25600000000000000000000), D1 := ((25299406188660714287963 : Rat) / 25600000000000000000000), D2 := ((6343632748660714287963 : Rat) / 25600000000000000000000), D3 := ((3346372588660714287963 : Rat) / 25600000000000000000000), D4 := ((166075642589285060559 : Rat) / 6400000000000000000000), LB := ((12288917610482897 : Rat) / 5000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71826768748660714287963 : Rat) / 25600000000000000000000), R := ((35916892102410714286841 : Rat) / 12800000000000000000000), D0 := ((35916892102410714286841 : Rat) / 12800000000000000000000), D1 := ((12653210822410714286841 : Rat) / 12800000000000000000000), D2 := ((3175324102410714286841 : Rat) / 12800000000000000000000), D3 := ((1676694022410714286841 : Rat) / 12800000000000000000000), D4 := ((657287114196425956517 : Rat) / 25600000000000000000000), LB := ((1240888328980061 : Rat) / 500000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35916892102410714286841 : Rat) / 12800000000000000000000), R := ((71840799660982142859401 : Rat) / 25600000000000000000000), D0 := ((71840799660982142859401 : Rat) / 25600000000000000000000), D1 := ((25313437100982142859401 : Rat) / 25600000000000000000000), D2 := ((6357663660982142859401 : Rat) / 25600000000000000000000), D3 := ((3360403500982142859401 : Rat) / 25600000000000000000000), D4 := ((325135829017855835399 : Rat) / 12800000000000000000000), LB := ((12676713051314459 : Rat) / 5000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71840799660982142859401 : Rat) / 25600000000000000000000), R := ((449048844482142857157 : Rat) / 160000000000000000000), D0 := ((449048844482142857157 : Rat) / 160000000000000000000), D1 := ((158252828482142857157 : Rat) / 160000000000000000000), D2 := ((39779244482142857157 : Rat) / 160000000000000000000), D3 := ((21046368482142857157 : Rat) / 160000000000000000000), D4 := ((643256201874997385079 : Rat) / 25600000000000000000000), LB := ((13095534474946713 : Rat) / 5000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((449048844482142857157 : Rat) / 160000000000000000000), R := ((35930923014732142858279 : Rat) / 12800000000000000000000), D0 := ((35930923014732142858279 : Rat) / 12800000000000000000000), D1 := ((12667241734732142858279 : Rat) / 12800000000000000000000), D2 := ((3189355014732142858279 : Rat) / 12800000000000000000000), D3 := ((1690724934732142858279 : Rat) / 12800000000000000000000), D4 := ((3976504660714269371 : Rat) / 160000000000000000000), LB := ((3595114971421953 : Rat) / 50000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35930923014732142858279 : Rat) / 12800000000000000000000), R := ((17968969235446428571999 : Rat) / 6400000000000000000000), D0 := ((17968969235446428571999 : Rat) / 6400000000000000000000), D1 := ((6337128595446428571999 : Rat) / 6400000000000000000000), D2 := ((1598185235446428571999 : Rat) / 6400000000000000000000), D3 := ((848870195446428571999 : Rat) / 6400000000000000000000), D4 := ((311104916696427263961 : Rat) / 12800000000000000000000), LB := ((19889226786856673 : Rat) / 50000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17968969235446428571999 : Rat) / 6400000000000000000000), R := ((35944953927053571429717 : Rat) / 12800000000000000000000), D0 := ((35944953927053571429717 : Rat) / 12800000000000000000000), D1 := ((12681272647053571429717 : Rat) / 12800000000000000000000), D2 := ((3203385927053571429717 : Rat) / 12800000000000000000000), D3 := ((1704755847053571429717 : Rat) / 12800000000000000000000), D4 := ((152044730267856489121 : Rat) / 6400000000000000000000), LB := ((8553524540358959 : Rat) / 10000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35944953927053571429717 : Rat) / 12800000000000000000000), R := ((8987992345803571428859 : Rat) / 3200000000000000000000), D0 := ((8987992345803571428859 : Rat) / 3200000000000000000000), D1 := ((3172072025803571428859 : Rat) / 3200000000000000000000), D2 := ((802600345803571428859 : Rat) / 3200000000000000000000), D3 := ((427942825803571428859 : Rat) / 3200000000000000000000), D4 := ((297074004374998692523 : Rat) / 12800000000000000000000), LB := ((725308068031727 : Rat) / 500000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8987992345803571428859 : Rat) / 3200000000000000000000), R := ((7191796967875000000231 : Rat) / 2560000000000000000000), D0 := ((7191796967875000000231 : Rat) / 2560000000000000000000), D1 := ((2539060711875000000231 : Rat) / 2560000000000000000000), D2 := ((643483367875000000231 : Rat) / 2560000000000000000000), D3 := ((343757351875000000231 : Rat) / 2560000000000000000000), D4 := ((72514637053571101701 : Rat) / 3200000000000000000000), LB := ((2190016707910969 : Rat) / 1000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((7191796967875000000231 : Rat) / 2560000000000000000000), R := ((17983000147767857143437 : Rat) / 6400000000000000000000), D0 := ((17983000147767857143437 : Rat) / 6400000000000000000000), D1 := ((6351159507767857143437 : Rat) / 6400000000000000000000), D2 := ((1612216147767857143437 : Rat) / 6400000000000000000000), D3 := ((862901107767857143437 : Rat) / 6400000000000000000000), D4 := ((56608618410714024217 : Rat) / 2560000000000000000000), LB := ((1925292815752877 : Rat) / 625000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17983000147767857143437 : Rat) / 6400000000000000000000), R := ((35973015751696428572593 : Rat) / 12800000000000000000000), D0 := ((35973015751696428572593 : Rat) / 12800000000000000000000), D1 := ((12709334471696428572593 : Rat) / 12800000000000000000000), D2 := ((3231447751696428572593 : Rat) / 12800000000000000000000), D3 := ((1732817671696428572593 : Rat) / 12800000000000000000000), D4 := ((138013817946427917683 : Rat) / 6400000000000000000000), LB := ((4129406508423417 : Rat) / 1000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35973015751696428572593 : Rat) / 12800000000000000000000), R := ((4497503900982142857289 : Rat) / 1600000000000000000000), D0 := ((4497503900982142857289 : Rat) / 1600000000000000000000), D1 := ((1589543740982142857289 : Rat) / 1600000000000000000000), D2 := ((404807900982142857289 : Rat) / 1600000000000000000000), D3 := ((217479140982142857289 : Rat) / 1600000000000000000000), D4 := ((269012179732141549647 : Rat) / 12800000000000000000000), LB := ((534483985367229 : Rat) / 100000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4497503900982142857289 : Rat) / 1600000000000000000000), R := ((143976248480714285719 : Rat) / 51200000000000000000), D0 := ((143976248480714285719 : Rat) / 51200000000000000000), D1 := ((50921523360714285719 : Rat) / 51200000000000000000), D2 := ((13009976480714285719 : Rat) / 51200000000000000000), D3 := ((7015456160714285719 : Rat) / 51200000000000000000), D4 := ((32749590446428407991 : Rat) / 1600000000000000000000), LB := ((14368542126076411 : Rat) / 10000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((143976248480714285719 : Rat) / 51200000000000000000), R := ((9002023258125000000297 : Rat) / 3200000000000000000000), D0 := ((9002023258125000000297 : Rat) / 3200000000000000000000), D1 := ((3186102938125000000297 : Rat) / 3200000000000000000000), D2 := ((816631258125000000297 : Rat) / 3200000000000000000000), D3 := ((441973738125000000297 : Rat) / 3200000000000000000000), D4 := ((24796581124999869249 : Rat) / 1280000000000000000000), LB := ((4787283496780703 : Rat) / 1000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((9002023258125000000297 : Rat) / 3200000000000000000000), R := ((18011061972410714286313 : Rat) / 6400000000000000000000), D0 := ((18011061972410714286313 : Rat) / 6400000000000000000000), D1 := ((6379221332410714286313 : Rat) / 6400000000000000000000), D2 := ((1640277972410714286313 : Rat) / 6400000000000000000000), D3 := ((890962932410714286313 : Rat) / 6400000000000000000000), D4 := ((58483724732142530263 : Rat) / 3200000000000000000000), LB := ((8961132506947411 : Rat) / 1000000000000000000) },
  { w1 := ((578662397335841 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((126624342640707 : Rat) / 500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18011061972410714286313 : Rat) / 6400000000000000000000), R := ((140766229910714285719 : Rat) / 50000000000000000000), D0 := ((140766229910714285719 : Rat) / 50000000000000000000), D1 := ((49892474910714285719 : Rat) / 50000000000000000000), D2 := ((12869479910714285719 : Rat) / 50000000000000000000), D3 := ((7015456160714285719 : Rat) / 50000000000000000000), D4 := ((109951993303570774807 : Rat) / 6400000000000000000000), LB := ((7029399464247743 : Rat) / 500000000000000000) }
]

def block011RightChunk000L : Rat := ((22689113839285714287 : Rat) / 12500000000000000000)
def block011RightChunk000R : Rat := ((140766229910714285719 : Rat) / 50000000000000000000)

def block011RightChunk000Certificate : Bool :=
  allBoxesValid block011RightChunk000 &&
  coversFromBool block011RightChunk000 block011RightChunk000L block011RightChunk000R

theorem block011RightChunk000Certificate_eq_true :
    block011RightChunk000Certificate = true := by
  native_decide

def block011RightChainCertificate : Bool :=
  decide (
    block011RightL = ((22689113839285714287 : Rat) / 12500000000000000000) /\
    ((140766229910714285719 : Rat) / 50000000000000000000) = block011RightR)

theorem block011RightChainCertificate_eq_true :
    block011RightChainCertificate = true := by
  native_decide

def block011LeftBoxCount : Nat := boxCount block011LeftBoxes
def block011RightBoxCount : Nat := 43

def block011_rational_certificate : Prop :=
    block011LeftCertificate = true /\
    block011RightChainCertificate = true /\
    block011RightChunk000Certificate = true

theorem block011_rational_certificate_proof :
    block011_rational_certificate := by
  exact ⟨block011LeftCertificate_eq_true, block011RightChainCertificate_eq_true, block011RightChunk000Certificate_eq_true⟩

end Block011
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block011

open Set

def block011W1 : Rat := ((578662397335841 : Rat) / 62500000000000)
def block011W2 : Rat := (0 : Rat)
def block011W3 : Rat := (0 : Rat)
def block011W4 : Rat := ((126624342640707 : Rat) / 500000000000000)
def block011S1 : Rat := ((18174751 : Rat) / 10000000)
def block011S2 : Rat := ((511587 : Rat) / 200000)
def block011S3 : Rat := ((107000619 : Rat) / 40000000)
def block011S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block011V (y : ℝ) : ℝ :=
  ratPotential block011W1 block011W2 block011W3 block011W4 block011S1 block011S2 block011S3 block011S4 y

def block011LeftParamsCertificate : Bool :=
  allBoxesSameParams block011LeftBoxes block011W1 block011W2 block011W3 block011W4 block011S1 block011S2 block011S3 block011S4

theorem block011LeftParamsCertificate_eq_true :
    block011LeftParamsCertificate = true := by
  native_decide

theorem block011_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block011LeftL : ℝ) (block011LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block011S1 : ℝ))
    (hy2ne : y ≠ (block011S2 : ℝ))
    (hy3ne : y ≠ (block011S3 : ℝ))
    (hy4ne : y ≠ (block011S4 : ℝ)) :
    0 < block011V y := by
  have hcert := block011LeftCertificate_eq_true
  unfold block011LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block011LeftBoxes) (lo := block011LeftL) (hi := block011LeftR)
    (w1 := block011W1) (w2 := block011W2) (w3 := block011W3) (w4 := block011W4)
    (s1 := block011S1) (s2 := block011S2) (s3 := block011S3) (s4 := block011S4)
    hboxes hcover block011LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block011RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block011RightChunk000 block011W1 block011W2 block011W3 block011W4 block011S1 block011S2 block011S3 block011S4

theorem block011RightChunk000ParamsCertificate_eq_true :
    block011RightChunk000ParamsCertificate = true := by
  native_decide

theorem block011_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block011RightChunk000L : ℝ) (block011RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block011S1 : ℝ))
    (hy2ne : y ≠ (block011S2 : ℝ))
    (hy3ne : y ≠ (block011S3 : ℝ))
    (hy4ne : y ≠ (block011S4 : ℝ)) :
    0 < block011V y := by
  have hcert := block011RightChunk000Certificate_eq_true
  unfold block011RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block011RightChunk000) (lo := block011RightChunk000L) (hi := block011RightChunk000R)
    (w1 := block011W1) (w2 := block011W2) (w3 := block011W3) (w4 := block011W4)
    (s1 := block011S1) (s2 := block011S2) (s3 := block011S3) (s4 := block011S4)
    hboxes hcover block011RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block011_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block011RightL : ℝ) (block011RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block011S1 : ℝ))
    (hy2ne : y ≠ (block011S2 : ℝ))
    (hy3ne : y ≠ (block011S3 : ℝ))
    (hy4ne : y ≠ (block011S4 : ℝ)) :
    0 < block011V y := by
  have hL : (block011RightChunk000L : ℝ) = (block011RightL : ℝ) := by
    norm_num [block011RightChunk000L, block011RightL]
  have hR : (block011RightChunk000R : ℝ) = (block011RightR : ℝ) := by
    norm_num [block011RightChunk000R, block011RightR]
  have hyc : y ∈ Icc (block011RightChunk000L : ℝ) (block011RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block011_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block011_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block011LeftL : ℝ) (block011LeftR : ℝ) →
    y ≠ 0 → y ≠ (block011S1 : ℝ) → y ≠ (block011S2 : ℝ) →
    y ≠ (block011S3 : ℝ) → y ≠ (block011S4 : ℝ) → 0 < block011V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block011RightL : ℝ) (block011RightR : ℝ) →
    y ≠ 0 → y ≠ (block011S1 : ℝ) → y ≠ (block011S2 : ℝ) →
    y ≠ (block011S3 : ℝ) → y ≠ (block011S4 : ℝ) → 0 < block011V y)

theorem block011_reallog_certificate_proof :
    block011_reallog_certificate := by
  exact ⟨block011_left_V_pos, block011_right_V_pos⟩

end Block011
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block011.block011V
#check Erdos1038Lean.M1817475.Block011.block011_left_V_pos
#check Erdos1038Lean.M1817475.Block011.block011_right_V_pos
#check Erdos1038Lean.M1817475.Block011.block011_reallog_certificate_proof
