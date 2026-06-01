/-
Self-contained Lean4Web paste file.
Block 388 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block388

def block388LeftL : Rat := ((37071448660714285881 : Rat) / 50000000000000000000)
def block388LeftR : Rat := ((9270305803571428613 : Rat) / 12500000000000000000)
def block388RightL : Rat := ((87071448660714285881 : Rat) / 50000000000000000000)
def block388RightR : Rat := ((34270305803571428613 : Rat) / 12500000000000000000)

def block388LeftBoxes : List RatBox := [
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((37071448660714285881 : Rat) / 50000000000000000000), R := ((9270305803571428613 : Rat) / 12500000000000000000), D0 := ((9270305803571428613 : Rat) / 12500000000000000000), D1 := ((53802306339285714119 : Rat) / 50000000000000000000), D2 := ((90825301339285714119 : Rat) / 50000000000000000000), D3 := ((47738527499999999943 : Rat) / 25000000000000000000), D4 := ((102035785446428566267 : Rat) / 50000000000000000000), LB := ((3874343835944677 : Rat) / 5000000000000000000) }
]

def block388LeftCertificate : Bool :=
  allBoxesValid block388LeftBoxes &&
  coversFromBool block388LeftBoxes block388LeftL block388LeftR

theorem block388LeftCertificate_eq_true :
    block388LeftCertificate = true := by
  native_decide

def block388RightChunk000 : List RatBox := [
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((87071448660714285881 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3802306339285714119 : Rat) / 50000000000000000000), D2 := ((40825301339285714119 : Rat) / 50000000000000000000), D3 := ((22738527499999999943 : Rat) / 25000000000000000000), D4 := ((52035785446428566267 : Rat) / 50000000000000000000), LB := ((3771133639290281 : Rat) / 2500000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41674748660714285767 : Rat) / 50000000000000000000), D4 := ((12058369776785713037 : Rat) / 12500000000000000000), LB := ((7079471125485383 : Rat) / 100000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23163251160714285767 : Rat) / 50000000000000000000), D4 := ((7430495401785713037 : Rat) / 12500000000000000000), LB := ((1195764770311011 : Rat) / 25000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18535376785714285767 : Rat) / 50000000000000000000), D4 := ((6273526808035713037 : Rat) / 12500000000000000000), LB := ((2505072183807261 : Rat) / 100000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16221439598214285767 : Rat) / 50000000000000000000), D4 := ((5695042511160713037 : Rat) / 12500000000000000000), LB := ((2349457733283107 : Rat) / 100000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((15064471004464285767 : Rat) / 50000000000000000000), D4 := ((5405800362723213037 : Rat) / 12500000000000000000), LB := ((3774387553276831 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13907502410714285767 : Rat) / 50000000000000000000), D4 := ((5116558214285713037 : Rat) / 12500000000000000000), LB := ((2175926535952881 : Rat) / 250000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((13329018113839285767 : Rat) / 50000000000000000000), D4 := ((4971937140066963037 : Rat) / 12500000000000000000), LB := ((3163509361936101 : Rat) / 2000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((766707007 : Rat) / 320000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12750533816964285767 : Rat) / 50000000000000000000), D4 := ((4827316065848213037 : Rat) / 12500000000000000000), LB := ((29116655015093 : Rat) / 5000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((12461291668526785767 : Rat) / 50000000000000000000), D4 := ((4755005528738838037 : Rat) / 12500000000000000000), LB := ((6097706228516353 : Rat) / 2000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12172049520089285767 : Rat) / 50000000000000000000), D4 := ((4682694991629463037 : Rat) / 12500000000000000000), LB := ((5403828390182497 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((123561673 : Rat) / 51200000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11882807371651785767 : Rat) / 50000000000000000000), D4 := ((4610384454520088037 : Rat) / 12500000000000000000), LB := ((3406826088758419 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((11738186297433035767 : Rat) / 50000000000000000000), D4 := ((4574229185965400537 : Rat) / 12500000000000000000), LB := ((4750852298029129 : Rat) / 2000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((387055803 : Rat) / 160000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11593565223214285767 : Rat) / 50000000000000000000), D4 := ((4538073917410713037 : Rat) / 12500000000000000000), LB := ((14164035178760859 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((11448944148995535767 : Rat) / 50000000000000000000), D4 := ((4501918648856025537 : Rat) / 12500000000000000000), LB := ((2655491094976231 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11304323074776785767 : Rat) / 50000000000000000000), D4 := ((4465763380301338037 : Rat) / 12500000000000000000), LB := ((2798449370854661 : Rat) / 1250000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((11232012537667410767 : Rat) / 50000000000000000000), D4 := ((4447685746023994287 : Rat) / 12500000000000000000), LB := ((9287059529243663 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((11159702000558035767 : Rat) / 50000000000000000000), D4 := ((4429608111746650537 : Rat) / 12500000000000000000), LB := ((3738599352447053 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((11087391463448660767 : Rat) / 50000000000000000000), D4 := ((4411530477469306787 : Rat) / 12500000000000000000), LB := ((720652802117909 : Rat) / 625000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11015080926339285767 : Rat) / 50000000000000000000), D4 := ((4393452843191963037 : Rat) / 12500000000000000000), LB := ((332173442581829 : Rat) / 400000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((10942770389229910767 : Rat) / 50000000000000000000), D4 := ((4375375208914619287 : Rat) / 12500000000000000000), LB := ((1319551997987639 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10870459852120535767 : Rat) / 50000000000000000000), D4 := ((4357297574637275537 : Rat) / 12500000000000000000), LB := ((24542620155737493 : Rat) / 100000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((24941877169 : Rat) / 10240000000), D0 := ((24941877169 : Rat) / 10240000000), D1 := ((1266186429 : Rat) / 2048000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((10798149315011160767 : Rat) / 50000000000000000000), D4 := ((4339219940359931787 : Rat) / 12500000000000000000), LB := ((12272453630648439 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24941877169 : Rat) / 10240000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((1251377231 : Rat) / 10240000000), D3 := ((10761994046456473267 : Rat) / 50000000000000000000), D4 := ((541272640402657489 : Rat) / 1562500000000000000), LB := ((11028165910640653 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((24956686367 : Rat) / 10240000000), D0 := ((24956686367 : Rat) / 10240000000), D1 := ((6345741343 : Rat) / 10240000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10725838777901785767 : Rat) / 50000000000000000000), D4 := ((4321142306082588037 : Rat) / 12500000000000000000), LB := ((1967179890013493 : Rat) / 2000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24956686367 : Rat) / 10240000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((1236568033 : Rat) / 10240000000), D3 := ((10689683509347098267 : Rat) / 50000000000000000000), D4 := ((2156051744471958081 : Rat) / 6250000000000000000), LB := ((271748679142687 : Rat) / 312500000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((4994299113 : Rat) / 2048000000), D0 := ((4994299113 : Rat) / 2048000000), D1 := ((6360550541 : Rat) / 10240000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((10653528240792410767 : Rat) / 50000000000000000000), D4 := ((4303064671805244287 : Rat) / 12500000000000000000), LB := ((3804324472167081 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4994299113 : Rat) / 2048000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((244351767 : Rat) / 2048000000), D3 := ((10617372972237723267 : Rat) / 50000000000000000000), D4 := ((1073506463666643103 : Rat) / 3125000000000000000), LB := ((6574286068611601 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((24986304763 : Rat) / 10240000000), D0 := ((24986304763 : Rat) / 10240000000), D1 := ((6375359739 : Rat) / 10240000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10581217703683035767 : Rat) / 50000000000000000000), D4 := ((4284987037527900537 : Rat) / 12500000000000000000), LB := ((5593186982820741 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24986304763 : Rat) / 10240000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((1206949637 : Rat) / 10240000000), D3 := ((10545062435128348267 : Rat) / 50000000000000000000), D4 := ((2137974110194614331 : Rat) / 6250000000000000000), LB := ((1458023299469053 : Rat) / 3125000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((25001113961 : Rat) / 10240000000), D0 := ((25001113961 : Rat) / 10240000000), D1 := ((6390168937 : Rat) / 10240000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((10508907166573660767 : Rat) / 50000000000000000000), D4 := ((4266909403250556787 : Rat) / 12500000000000000000), LB := ((3792076762992591 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25001113961 : Rat) / 10240000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((1192140439 : Rat) / 10240000000), D3 := ((10472751898018973267 : Rat) / 50000000000000000000), D4 := ((266116911631992807 : Rat) / 781250000000000000), LB := ((7431816917260331 : Rat) / 25000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((156303241 : Rat) / 64000000), R := ((25015923159 : Rat) / 10240000000), D0 := ((25015923159 : Rat) / 10240000000), D1 := ((1280995627 : Rat) / 2048000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10436596629464285767 : Rat) / 50000000000000000000), D4 := ((4248831768973213037 : Rat) / 12500000000000000000), LB := ((2207963050671613 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25015923159 : Rat) / 10240000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((1177331241 : Rat) / 10240000000), D3 := ((10400441360909598267 : Rat) / 50000000000000000000), D4 := ((2119896475917270581 : Rat) / 6250000000000000000), LB := ((7490647585833843 : Rat) / 50000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((25030732357 : Rat) / 10240000000), D0 := ((25030732357 : Rat) / 10240000000), D1 := ((6419787333 : Rat) / 10240000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((10364286092354910767 : Rat) / 50000000000000000000), D4 := ((4230754134695869287 : Rat) / 12500000000000000000), LB := ((2108939015931649 : Rat) / 25000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25030732357 : Rat) / 10240000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((1162522043 : Rat) / 10240000000), D3 := ((10328130823800223267 : Rat) / 50000000000000000000), D4 := ((1055428829389299353 : Rat) / 3125000000000000000), LB := ((489312827171573 : Rat) / 20000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((50083678511 : Rat) / 20480000000), D0 := ((50083678511 : Rat) / 20480000000), D1 := ((12861788463 : Rat) / 20480000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10291975555245535767 : Rat) / 50000000000000000000), D4 := ((4212676500418525537 : Rat) / 12500000000000000000), LB := ((146063726905947 : Rat) / 250000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50083678511 : Rat) / 20480000000), R := ((5009108311 : Rat) / 2048000000), D0 := ((5009108311 : Rat) / 2048000000), D1 := ((6434596531 : Rat) / 10240000000), D2 := ((2302830289 : Rat) / 20480000000), D3 := ((10273897920968192017 : Rat) / 50000000000000000000), D4 := ((8416314183698379199 : Rat) / 25000000000000000000), LB := ((2794649795230253 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5009108311 : Rat) / 2048000000), R := ((50098487709 : Rat) / 20480000000), D0 := ((50098487709 : Rat) / 20480000000), D1 := ((12876597661 : Rat) / 20480000000), D2 := ((229542569 : Rat) / 2048000000), D3 := ((10255820286690848267 : Rat) / 50000000000000000000), D4 := ((2101818841639926831 : Rat) / 6250000000000000000), LB := ((5350190158920631 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50098487709 : Rat) / 20480000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((2288021091 : Rat) / 20480000000), D3 := ((10237742652413504517 : Rat) / 50000000000000000000), D4 := ((8398236549421035449 : Rat) / 25000000000000000000), LB := ((1281316891618839 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((50113296907 : Rat) / 20480000000), D0 := ((50113296907 : Rat) / 20480000000), D1 := ((12891406859 : Rat) / 20480000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((10219665018136160767 : Rat) / 50000000000000000000), D4 := ((4194598866141181787 : Rat) / 12500000000000000000), LB := ((4914578983203077 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50113296907 : Rat) / 20480000000), R := ((25060350753 : Rat) / 10240000000), D0 := ((25060350753 : Rat) / 10240000000), D1 := ((6449405729 : Rat) / 10240000000), D2 := ((2273211893 : Rat) / 20480000000), D3 := ((10201587383858817017 : Rat) / 50000000000000000000), D4 := ((8380158915143691699 : Rat) / 25000000000000000000), LB := ((4718171968676743 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25060350753 : Rat) / 10240000000), R := ((10025621221 : Rat) / 4096000000), D0 := ((10025621221 : Rat) / 4096000000), D1 := ((12906216057 : Rat) / 20480000000), D2 := ((1132903647 : Rat) / 10240000000), D3 := ((10183509749581473267 : Rat) / 50000000000000000000), D4 := ((523195006125313739 : Rat) / 1562500000000000000), LB := ((2268047238119797 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10025621221 : Rat) / 4096000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 4096000000), D3 := ((10165432115304129517 : Rat) / 50000000000000000000), D4 := ((8362081280866347949 : Rat) / 25000000000000000000), LB := ((1092098714350967 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((50142915303 : Rat) / 20480000000), D0 := ((50142915303 : Rat) / 20480000000), D1 := ((2584205051 : Rat) / 4096000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10147354481026785767 : Rat) / 50000000000000000000), D4 := ((4176521231863838037 : Rat) / 12500000000000000000), LB := ((2107560933136271 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50142915303 : Rat) / 20480000000), R := ((25075159951 : Rat) / 10240000000), D0 := ((25075159951 : Rat) / 10240000000), D1 := ((6464214927 : Rat) / 10240000000), D2 := ((2243593497 : Rat) / 20480000000), D3 := ((10129276846749442017 : Rat) / 50000000000000000000), D4 := ((8344003646589004199 : Rat) / 25000000000000000000), LB := ((20381623320216147 : Rat) / 50000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25075159951 : Rat) / 10240000000), R := ((50157724501 : Rat) / 20480000000), D0 := ((50157724501 : Rat) / 20480000000), D1 := ((12935834453 : Rat) / 20480000000), D2 := ((1118094449 : Rat) / 10240000000), D3 := ((10111199212472098267 : Rat) / 50000000000000000000), D4 := ((2083741207362583081 : Rat) / 6250000000000000000), LB := ((4940066029518117 : Rat) / 12500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50157724501 : Rat) / 20480000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((2228784299 : Rat) / 20480000000), D3 := ((10093121578194754517 : Rat) / 50000000000000000000), D4 := ((8325926012311660449 : Rat) / 25000000000000000000), LB := ((960589083544433 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((501651291 : Rat) / 204800000), R := ((50172533699 : Rat) / 20480000000), D0 := ((50172533699 : Rat) / 20480000000), D1 := ((12950643651 : Rat) / 20480000000), D2 := ((22213797 : Rat) / 204800000), D3 := ((10075043943917410767 : Rat) / 50000000000000000000), D4 := ((4158443597586494287 : Rat) / 12500000000000000000), LB := ((37472856059717063 : Rat) / 100000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50172533699 : Rat) / 20480000000), R := ((25089969149 : Rat) / 10240000000), D0 := ((25089969149 : Rat) / 10240000000), D1 := ((51832193 : Rat) / 81920000), D2 := ((2213975101 : Rat) / 20480000000), D3 := ((10056966309640067017 : Rat) / 50000000000000000000), D4 := ((8307848378034316699 : Rat) / 25000000000000000000), LB := ((458361434384387 : Rat) / 1250000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25089969149 : Rat) / 10240000000), R := ((50187342897 : Rat) / 20480000000), D0 := ((50187342897 : Rat) / 20480000000), D1 := ((12965452849 : Rat) / 20480000000), D2 := ((1103285251 : Rat) / 10240000000), D3 := ((10038888675362723267 : Rat) / 50000000000000000000), D4 := ((1037351195111955603 : Rat) / 3125000000000000000), LB := ((3601225208231529 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50187342897 : Rat) / 20480000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((2199165903 : Rat) / 20480000000), D3 := ((10020811041085379517 : Rat) / 50000000000000000000), D4 := ((8289770743756972949 : Rat) / 25000000000000000000), LB := ((8875846269575799 : Rat) / 25000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((10040430419 : Rat) / 4096000000), D0 := ((10040430419 : Rat) / 4096000000), D1 := ((12980262047 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10002733406808035767 : Rat) / 50000000000000000000), D4 := ((4140365963309150537 : Rat) / 12500000000000000000), LB := ((1757141758441383 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10040430419 : Rat) / 4096000000), R := ((25104778347 : Rat) / 10240000000), D0 := ((25104778347 : Rat) / 10240000000), D1 := ((6493833323 : Rat) / 10240000000), D2 := ((436871341 : Rat) / 4096000000), D3 := ((9984655772530692017 : Rat) / 50000000000000000000), D4 := ((8271693109479629199 : Rat) / 25000000000000000000), LB := ((1746556412080269 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25104778347 : Rat) / 10240000000), R := ((50216961293 : Rat) / 20480000000), D0 := ((50216961293 : Rat) / 20480000000), D1 := ((2599014249 : Rat) / 4096000000), D2 := ((1088476053 : Rat) / 10240000000), D3 := ((9966578138253348267 : Rat) / 50000000000000000000), D4 := ((2065663573085239331 : Rat) / 6250000000000000000), LB := ((174343973466079 : Rat) / 500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50216961293 : Rat) / 20480000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((2169547507 : Rat) / 20480000000), D3 := ((9948500503976004517 : Rat) / 50000000000000000000), D4 := ((8253615475202285449 : Rat) / 25000000000000000000), LB := ((34956369481883853 : Rat) / 100000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((50231770491 : Rat) / 20480000000), D0 := ((50231770491 : Rat) / 20480000000), D1 := ((13009880443 : Rat) / 20480000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((9930422869698660767 : Rat) / 50000000000000000000), D4 := ((4122288329031806787 : Rat) / 12500000000000000000), LB := ((1759719609042143 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50231770491 : Rat) / 20480000000), R := ((5023917509 : Rat) / 2048000000), D0 := ((5023917509 : Rat) / 2048000000), D1 := ((6508642521 : Rat) / 10240000000), D2 := ((2154738309 : Rat) / 20480000000), D3 := ((9912345235421317017 : Rat) / 50000000000000000000), D4 := ((8235537840924941699 : Rat) / 25000000000000000000), LB := ((35583407032660497 : Rat) / 100000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5023917509 : Rat) / 2048000000), R := ((50246579689 : Rat) / 20480000000), D0 := ((50246579689 : Rat) / 20480000000), D1 := ((13024689641 : Rat) / 20480000000), D2 := ((214733371 : Rat) / 2048000000), D3 := ((9894267601143973267 : Rat) / 50000000000000000000), D4 := ((64269523623330233 : Rat) / 195312500000000000), LB := ((36123963004189297 : Rat) / 100000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50246579689 : Rat) / 20480000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((2139929111 : Rat) / 20480000000), D3 := ((9876189966866629517 : Rat) / 50000000000000000000), D4 := ((8217460206647597949 : Rat) / 25000000000000000000), LB := ((3681661384244139 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((50261388887 : Rat) / 20480000000), D0 := ((50261388887 : Rat) / 20480000000), D1 := ((13039498839 : Rat) / 20480000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9858112332589285767 : Rat) / 50000000000000000000), D4 := ((4104210694754463037 : Rat) / 12500000000000000000), LB := ((1883095906589083 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50261388887 : Rat) / 20480000000), R := ((25134396743 : Rat) / 10240000000), D0 := ((25134396743 : Rat) / 10240000000), D1 := ((6523451719 : Rat) / 10240000000), D2 := ((2125119913 : Rat) / 20480000000), D3 := ((9840034698311942017 : Rat) / 50000000000000000000), D4 := ((8199382572370254199 : Rat) / 25000000000000000000), LB := ((19330219675660343 : Rat) / 50000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25134396743 : Rat) / 10240000000), R := ((10055239617 : Rat) / 4096000000), D0 := ((10055239617 : Rat) / 4096000000), D1 := ((13054308037 : Rat) / 20480000000), D2 := ((1058857657 : Rat) / 10240000000), D3 := ((9821957064034598267 : Rat) / 50000000000000000000), D4 := ((2047585938807895581 : Rat) / 6250000000000000000), LB := ((19906372967004593 : Rat) / 50000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10055239617 : Rat) / 4096000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((422062143 : Rat) / 4096000000), D3 := ((9803879429757254517 : Rat) / 50000000000000000000), D4 := ((8181304938092910449 : Rat) / 25000000000000000000), LB := ((4111941132603769 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((50291007283 : Rat) / 20480000000), D0 := ((50291007283 : Rat) / 20480000000), D1 := ((2613823447 : Rat) / 4096000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((9785801795479910767 : Rat) / 50000000000000000000), D4 := ((4086133060477119287 : Rat) / 12500000000000000000), LB := ((2129050702380647 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50291007283 : Rat) / 20480000000), R := ((25149205941 : Rat) / 10240000000), D0 := ((25149205941 : Rat) / 10240000000), D1 := ((6538260917 : Rat) / 10240000000), D2 := ((2095501517 : Rat) / 20480000000), D3 := ((9767724161202567017 : Rat) / 50000000000000000000), D4 := ((8163227303815566699 : Rat) / 25000000000000000000), LB := ((1104953443866949 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25149205941 : Rat) / 10240000000), R := ((50305816481 : Rat) / 20480000000), D0 := ((50305816481 : Rat) / 20480000000), D1 := ((13083926433 : Rat) / 20480000000), D2 := ((1044048459 : Rat) / 10240000000), D3 := ((9749646526925223267 : Rat) / 50000000000000000000), D4 := ((1019273560834611853 : Rat) / 3125000000000000000), LB := ((9194274260267421 : Rat) / 20000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50305816481 : Rat) / 20480000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((2080692319 : Rat) / 20480000000), D3 := ((9731568892647879517 : Rat) / 50000000000000000000), D4 := ((8145149669538222949 : Rat) / 25000000000000000000), LB := ((239506544018539 : Rat) / 500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((50320625679 : Rat) / 20480000000), D0 := ((50320625679 : Rat) / 20480000000), D1 := ((13098735631 : Rat) / 20480000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9713491258370535767 : Rat) / 50000000000000000000), D4 := ((4068055426199775537 : Rat) / 12500000000000000000), LB := ((31242843565411 : Rat) / 62500000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50320625679 : Rat) / 20480000000), R := ((25164015139 : Rat) / 10240000000), D0 := ((25164015139 : Rat) / 10240000000), D1 := ((1310614023 : Rat) / 2048000000), D2 := ((2065883121 : Rat) / 20480000000), D3 := ((9695413624093192017 : Rat) / 50000000000000000000), D4 := ((8127072035260879199 : Rat) / 25000000000000000000), LB := ((5223369883963769 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25164015139 : Rat) / 10240000000), R := ((50335434877 : Rat) / 20480000000), D0 := ((50335434877 : Rat) / 20480000000), D1 := ((13113544829 : Rat) / 20480000000), D2 := ((1029239261 : Rat) / 10240000000), D3 := ((9677335989815848267 : Rat) / 50000000000000000000), D4 := ((2029508304530551831 : Rat) / 6250000000000000000), LB := ((1365934162587193 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50335434877 : Rat) / 20480000000), R := ((12585709869 : Rat) / 5120000000), D0 := ((12585709869 : Rat) / 5120000000), D1 := ((3280237357 : Rat) / 5120000000), D2 := ((2051073923 : Rat) / 20480000000), D3 := ((9659258355538504517 : Rat) / 50000000000000000000), D4 := ((8108994400983535449 : Rat) / 25000000000000000000), LB := ((5720016851866461 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12585709869 : Rat) / 5120000000), R := ((2014009763 : Rat) / 819200000), D0 := ((2014009763 : Rat) / 819200000), D1 := ((13128354027 : Rat) / 20480000000), D2 := ((510917331 : Rat) / 5120000000), D3 := ((9641180721261160767 : Rat) / 50000000000000000000), D4 := ((4049977791922431787 : Rat) / 12500000000000000000), LB := ((5992272630409579 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2014009763 : Rat) / 819200000), R := ((25178824337 : Rat) / 10240000000), D0 := ((25178824337 : Rat) / 10240000000), D1 := ((6567879313 : Rat) / 10240000000), D2 := ((81450589 : Rat) / 819200000), D3 := ((9623103086983817017 : Rat) / 50000000000000000000), D4 := ((8090916766706191699 : Rat) / 25000000000000000000), LB := ((314028334730973 : Rat) / 500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25178824337 : Rat) / 10240000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((1014430063 : Rat) / 10240000000), D3 := ((9605025452706473267 : Rat) / 50000000000000000000), D4 := ((505117371847969989 : Rat) / 1562500000000000000), LB := ((27609642746145857 : Rat) / 500000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((5038726707 : Rat) / 2048000000), D0 := ((5038726707 : Rat) / 2048000000), D1 := ((6582688511 : Rat) / 10240000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9568870184151785767 : Rat) / 50000000000000000000), D4 := ((4031900157645088037 : Rat) / 12500000000000000000), LB := ((12151107962626861 : Rat) / 100000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5038726707 : Rat) / 2048000000), R := ((12600519067 : Rat) / 5120000000), D0 := ((12600519067 : Rat) / 5120000000), D1 := ((659009311 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 2048000000), D3 := ((9532714915597098267 : Rat) / 50000000000000000000), D4 := ((2011430670253208081 : Rat) / 6250000000000000000), LB := ((971598637983101 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12600519067 : Rat) / 5120000000), R := ((25208442733 : Rat) / 10240000000), D0 := ((25208442733 : Rat) / 10240000000), D1 := ((6597497709 : Rat) / 10240000000), D2 := ((496108133 : Rat) / 5120000000), D3 := ((9496559647042410767 : Rat) / 50000000000000000000), D4 := ((4013822523367744287 : Rat) / 12500000000000000000), LB := ((13684900052782223 : Rat) / 50000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25208442733 : Rat) / 10240000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((984811667 : Rat) / 10240000000), D3 := ((9460404378487723267 : Rat) / 50000000000000000000), D4 := ((1001195926557268103 : Rat) / 3125000000000000000), LB := ((44962457857671 : Rat) / 125000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((25223251931 : Rat) / 10240000000), D0 := ((25223251931 : Rat) / 10240000000), D1 := ((6612306907 : Rat) / 10240000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9424249109933035767 : Rat) / 50000000000000000000), D4 := ((3995744889090400537 : Rat) / 12500000000000000000), LB := ((35342147899943 : Rat) / 78125000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25223251931 : Rat) / 10240000000), R := ((2523065653 : Rat) / 1024000000), D0 := ((2523065653 : Rat) / 1024000000), D1 := ((3309855753 : Rat) / 5120000000), D2 := ((970002469 : Rat) / 10240000000), D3 := ((9388093841378348267 : Rat) / 50000000000000000000), D4 := ((1993353035975864331 : Rat) / 6250000000000000000), LB := ((2758966580746619 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2523065653 : Rat) / 1024000000), R := ((25238061129 : Rat) / 10240000000), D0 := ((25238061129 : Rat) / 10240000000), D1 := ((1325423221 : Rat) / 2048000000), D2 := ((96259787 : Rat) / 1024000000), D3 := ((9351938572823660767 : Rat) / 50000000000000000000), D4 := ((3977667254813056787 : Rat) / 12500000000000000000), LB := ((328999014209283 : Rat) / 500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25238061129 : Rat) / 10240000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((955193271 : Rat) / 10240000000), D3 := ((9315783304268973267 : Rat) / 50000000000000000000), D4 := ((248039277354649057 : Rat) / 781250000000000000), LB := ((771051627479119 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((197230201 : Rat) / 80000000), R := ((25252870327 : Rat) / 10240000000), D0 := ((25252870327 : Rat) / 10240000000), D1 := ((6641925303 : Rat) / 10240000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9279628035714285767 : Rat) / 50000000000000000000), D4 := ((3959589620535713037 : Rat) / 12500000000000000000), LB := ((8910132419713557 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25252870327 : Rat) / 10240000000), R := ((12630137463 : Rat) / 5120000000), D0 := ((12630137463 : Rat) / 5120000000), D1 := ((3324664951 : Rat) / 5120000000), D2 := ((940384073 : Rat) / 10240000000), D3 := ((9243472767159598267 : Rat) / 50000000000000000000), D4 := ((1975275401698520581 : Rat) / 6250000000000000000), LB := ((318107238350537 : Rat) / 312500000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12630137463 : Rat) / 5120000000), R := ((1010707181 : Rat) / 409600000), D0 := ((1010707181 : Rat) / 409600000), D1 := ((6656734501 : Rat) / 10240000000), D2 := ((466489737 : Rat) / 5120000000), D3 := ((9207317498604910767 : Rat) / 50000000000000000000), D4 := ((3941511986258369287 : Rat) / 12500000000000000000), LB := ((1151902874998001 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1010707181 : Rat) / 409600000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 81920000), D3 := ((9171162230050223267 : Rat) / 50000000000000000000), D4 := ((983118292279924353 : Rat) / 3125000000000000000), LB := ((6464775459843891 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((12644946661 : Rat) / 5120000000), D0 := ((12644946661 : Rat) / 5120000000), D1 := ((3339474149 : Rat) / 5120000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9135006961495535767 : Rat) / 50000000000000000000), D4 := ((3923434351981025537 : Rat) / 12500000000000000000), LB := ((12485601028416893 : Rat) / 50000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12644946661 : Rat) / 5120000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 5120000000), D3 := ((9062696424386160767 : Rat) / 50000000000000000000), D4 := ((3905356717703681787 : Rat) / 12500000000000000000), LB := ((5700218895087483 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((632617563 : Rat) / 256000000), R := ((12659755859 : Rat) / 5120000000), D0 := ((12659755859 : Rat) / 5120000000), D1 := ((3354283347 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((8990385887276785767 : Rat) / 50000000000000000000), D4 := ((3887279083426338037 : Rat) / 12500000000000000000), LB := ((919749590694463 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12659755859 : Rat) / 5120000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((436871341 : Rat) / 5120000000), D3 := ((8918075350167410767 : Rat) / 50000000000000000000), D4 := ((3869201449148994287 : Rat) / 12500000000000000000), LB := ((12994563058407183 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((12674565057 : Rat) / 5120000000), D0 := ((12674565057 : Rat) / 5120000000), D1 := ((673818509 : Rat) / 1024000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((8845764813058035767 : Rat) / 50000000000000000000), D4 := ((3851123814871650537 : Rat) / 12500000000000000000), LB := ((2137159059661907 : Rat) / 1250000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12674565057 : Rat) / 5120000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((422062143 : Rat) / 5120000000), D3 := ((8773454275948660767 : Rat) / 50000000000000000000), D4 := ((3833046180594306787 : Rat) / 12500000000000000000), LB := ((3441877032453 : Rat) / 1600000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8701143738839285767 : Rat) / 50000000000000000000), D4 := ((3814968546316963037 : Rat) / 12500000000000000000), LB := ((6758764527366179 : Rat) / 25000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((8556522664620535767 : Rat) / 50000000000000000000), D4 := ((3778813277762275537 : Rat) / 12500000000000000000), LB := ((6616955550494963 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8411901590401785767 : Rat) / 50000000000000000000), D4 := ((3742658009207588037 : Rat) / 12500000000000000000), LB := ((2512027857366761 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8267280516183035767 : Rat) / 50000000000000000000), D4 := ((3706502740652900537 : Rat) / 12500000000000000000), LB := ((3842540593978011 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8122659441964285767 : Rat) / 50000000000000000000), D4 := ((3670347472098213037 : Rat) / 12500000000000000000), LB := ((3460806294124097 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((7833417293526785767 : Rat) / 50000000000000000000), D4 := ((3598036934988838037 : Rat) / 12500000000000000000), LB := ((4160903920547493 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7544175145089285767 : Rat) / 50000000000000000000), D4 := ((3525726397879463037 : Rat) / 12500000000000000000), LB := ((65067322530583 : Rat) / 7812500000000000) }
]

def block388RightChunk000L : Rat := ((87071448660714285881 : Rat) / 50000000000000000000)
def block388RightChunk000R : Rat := ((3207515409 : Rat) / 1280000000)

def block388RightChunk000Certificate : Bool :=
  allBoxesValid block388RightChunk000 &&
  coversFromBool block388RightChunk000 block388RightChunk000L block388RightChunk000R

theorem block388RightChunk000Certificate_eq_true :
    block388RightChunk000Certificate = true := by
  native_decide

def block388RightChunk001 : List RatBox := [
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7254932996651785767 : Rat) / 50000000000000000000), D4 := ((3453415860770088037 : Rat) / 12500000000000000000), LB := ((13287593226104483 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6965690848214285767 : Rat) / 50000000000000000000), D4 := ((3381105323660713037 : Rat) / 12500000000000000000), LB := ((10195433572516427 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6387206551339285767 : Rat) / 50000000000000000000), D4 := ((3236484249441963037 : Rat) / 12500000000000000000), LB := ((1594314937745301 : Rat) / 62500000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5808722254464285767 : Rat) / 50000000000000000000), D4 := ((3091863175223213037 : Rat) / 12500000000000000000), LB := ((15172120242184589 : Rat) / 500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((511587 : Rat) / 200000), R := ((516238753660714285767 : Rat) / 200000000000000000000), D0 := ((516238753660714285767 : Rat) / 200000000000000000000), D1 := ((152743733660714285767 : Rat) / 200000000000000000000), D2 := ((4651753660714285767 : Rat) / 200000000000000000000), D3 := ((4651753660714285767 : Rat) / 50000000000000000000), D4 := ((2802621026785713037 : Rat) / 12500000000000000000), LB := ((962551628782149 : Rat) / 20000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((516238753660714285767 : Rat) / 200000000000000000000), R := ((260445253660714285767 : Rat) / 100000000000000000000), D0 := ((260445253660714285767 : Rat) / 100000000000000000000), D1 := ((78697743660714285767 : Rat) / 100000000000000000000), D2 := ((4651753660714285767 : Rat) / 100000000000000000000), D3 := ((13955260982142857301 : Rat) / 200000000000000000000), D4 := ((1607607310714284913 : Rat) / 8000000000000000000), LB := ((5099202366743097 : Rat) / 100000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((260445253660714285767 : Rat) / 100000000000000000000), R := ((132548503660714285767 : Rat) / 50000000000000000000), D0 := ((132548503660714285767 : Rat) / 50000000000000000000), D1 := ((41674748660714285767 : Rat) / 50000000000000000000), D2 := ((4651753660714285767 : Rat) / 50000000000000000000), D3 := ((4651753660714285767 : Rat) / 100000000000000000000), D4 := ((17769214553571418529 : Rat) / 100000000000000000000), LB := ((112276160143603 : Rat) / 2500000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((132548503660714285767 : Rat) / 50000000000000000000), R := ((269629726875000000219 : Rat) / 100000000000000000000), D0 := ((269629726875000000219 : Rat) / 100000000000000000000), D1 := ((87882216875000000219 : Rat) / 100000000000000000000), D2 := ((13836226875000000219 : Rat) / 100000000000000000000), D3 := ((906543910714285737 : Rat) / 20000000000000000000), D4 := ((6558730446428566381 : Rat) / 50000000000000000000), LB := ((8608002033670237 : Rat) / 500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((269629726875000000219 : Rat) / 100000000000000000000), R := ((1083051627053571429561 : Rat) / 400000000000000000000), D0 := ((1083051627053571429561 : Rat) / 400000000000000000000), D1 := ((356061587053571429561 : Rat) / 400000000000000000000), D2 := ((59877627053571429561 : Rat) / 400000000000000000000), D3 := ((906543910714285737 : Rat) / 16000000000000000000), D4 := ((8584741339285704077 : Rat) / 100000000000000000000), LB := ((2317389570407491 : Rat) / 100000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1083051627053571429561 : Rat) / 400000000000000000000), R := ((2170635973660714287807 : Rat) / 800000000000000000000), D0 := ((2170635973660714287807 : Rat) / 800000000000000000000), D1 := ((716655893660714287807 : Rat) / 800000000000000000000), D2 := ((124287973660714287807 : Rat) / 800000000000000000000), D3 := ((9971983017857143107 : Rat) / 160000000000000000000), D4 := ((29806245803571387623 : Rat) / 400000000000000000000), LB := ((2351062496420947 : Rat) / 125000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2170635973660714287807 : Rat) / 800000000000000000000), R := ((543792173303571429123 : Rat) / 200000000000000000000), D0 := ((543792173303571429123 : Rat) / 200000000000000000000), D1 := ((180297153303571429123 : Rat) / 200000000000000000000), D2 := ((32205173303571429123 : Rat) / 200000000000000000000), D3 := ((2719631732142857211 : Rat) / 40000000000000000000), D4 := ((55079772053571346561 : Rat) / 800000000000000000000), LB := ((6844408085323939 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((543792173303571429123 : Rat) / 200000000000000000000), R := ((4354870105982142861669 : Rat) / 1600000000000000000000), D0 := ((4354870105982142861669 : Rat) / 1600000000000000000000), D1 := ((1446909945982142861669 : Rat) / 1600000000000000000000), D2 := ((262174105982142861669 : Rat) / 1600000000000000000000), D3 := ((906543910714285737 : Rat) / 12800000000000000000), D4 := ((12636763124999979469 : Rat) / 200000000000000000000), LB := ((8102975680744473 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4354870105982142861669 : Rat) / 1600000000000000000000), R := ((2179701412767857145177 : Rat) / 800000000000000000000), D0 := ((2179701412767857145177 : Rat) / 800000000000000000000), D1 := ((725721332767857145177 : Rat) / 800000000000000000000), D2 := ((133353412767857145177 : Rat) / 800000000000000000000), D3 := ((11785070839285714581 : Rat) / 160000000000000000000), D4 := ((96561385446428407067 : Rat) / 1600000000000000000000), LB := ((3827090888058271 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2179701412767857145177 : Rat) / 800000000000000000000), R := ((4363935545089285719039 : Rat) / 1600000000000000000000), D0 := ((4363935545089285719039 : Rat) / 1600000000000000000000), D1 := ((1455975385089285719039 : Rat) / 1600000000000000000000), D2 := ((271239545089285719039 : Rat) / 1600000000000000000000), D3 := ((24476685589285714899 : Rat) / 320000000000000000000), D4 := ((46014332946428489191 : Rat) / 800000000000000000000), LB := ((2909062208010793 : Rat) / 20000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4363935545089285719039 : Rat) / 1600000000000000000000), R := ((8732403809732142866763 : Rat) / 3200000000000000000000), D0 := ((8732403809732142866763 : Rat) / 3200000000000000000000), D1 := ((2916483489732142866763 : Rat) / 3200000000000000000000), D2 := ((547011809732142866763 : Rat) / 3200000000000000000000), D3 := ((9971983017857143107 : Rat) / 128000000000000000000), D4 := ((87495946339285549697 : Rat) / 1600000000000000000000), LB := ((1128594776395181 : Rat) / 500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8732403809732142866763 : Rat) / 3200000000000000000000), R := ((1092117066160714286931 : Rat) / 400000000000000000000), D0 := ((1092117066160714286931 : Rat) / 400000000000000000000), D1 := ((365127026160714286931 : Rat) / 400000000000000000000), D2 := ((68943066160714286931 : Rat) / 400000000000000000000), D3 := ((6345807375000000159 : Rat) / 80000000000000000000), D4 := ((170459173124999670709 : Rat) / 3200000000000000000000), LB := ((4476238082588291 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1092117066160714286931 : Rat) / 400000000000000000000), R := ((17478405778125000019581 : Rat) / 6400000000000000000000), D0 := ((17478405778125000019581 : Rat) / 6400000000000000000000), D1 := ((5846565138125000019581 : Rat) / 6400000000000000000000), D2 := ((1107621778125000019581 : Rat) / 6400000000000000000000), D3 := ((102439461910714288281 : Rat) / 1280000000000000000000), D4 := ((20740806696428530253 : Rat) / 400000000000000000000), LB := ((2251428739376893 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17478405778125000019581 : Rat) / 6400000000000000000000), R := ((8741469248839285724133 : Rat) / 3200000000000000000000), D0 := ((8741469248839285724133 : Rat) / 3200000000000000000000), D1 := ((2925548928839285724133 : Rat) / 3200000000000000000000), D2 := ((556077248839285724133 : Rat) / 3200000000000000000000), D3 := ((51673002910714287009 : Rat) / 640000000000000000000), D4 := ((327320187589285055363 : Rat) / 6400000000000000000000), LB := ((16993279941595607 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8741469248839285724133 : Rat) / 3200000000000000000000), R := ((17487471217232142876951 : Rat) / 6400000000000000000000), D0 := ((17487471217232142876951 : Rat) / 6400000000000000000000), D1 := ((5855630577232142876951 : Rat) / 6400000000000000000000), D2 := ((1116687217232142876951 : Rat) / 6400000000000000000000), D3 := ((20850509946428571951 : Rat) / 256000000000000000000), D4 := ((161393734017856813339 : Rat) / 3200000000000000000000), LB := ((11895046050313107 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17487471217232142876951 : Rat) / 6400000000000000000000), R := ((4373000984196428576409 : Rat) / 1600000000000000000000), D0 := ((4373000984196428576409 : Rat) / 1600000000000000000000), D1 := ((1465040824196428576409 : Rat) / 1600000000000000000000), D2 := ((280304984196428576409 : Rat) / 1600000000000000000000), D3 := ((26289773410714286373 : Rat) / 320000000000000000000), D4 := ((318254748482142197993 : Rat) / 6400000000000000000000), LB := ((1445031568286903 : Rat) / 2000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4373000984196428576409 : Rat) / 1600000000000000000000), R := ((17496536656339285734321 : Rat) / 6400000000000000000000), D0 := ((17496536656339285734321 : Rat) / 6400000000000000000000), D1 := ((5864696016339285734321 : Rat) / 6400000000000000000000), D2 := ((1125752656339285734321 : Rat) / 6400000000000000000000), D3 := ((106065637553571431229 : Rat) / 1280000000000000000000), D4 := ((78430507232142692327 : Rat) / 1600000000000000000000), LB := ((1494793320397647 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17496536656339285734321 : Rat) / 6400000000000000000000), R := ((34997606032232142897327 : Rat) / 12800000000000000000000), D0 := ((34997606032232142897327 : Rat) / 12800000000000000000000), D1 := ((11733924752232142897327 : Rat) / 12800000000000000000000), D2 := ((2256038032232142897327 : Rat) / 12800000000000000000000), D3 := ((42607563803571429639 : Rat) / 512000000000000000000), D4 := ((309189309374999340623 : Rat) / 6400000000000000000000), LB := ((14596050269923 : Rat) / 12500000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((34997606032232142897327 : Rat) / 12800000000000000000000), R := ((8750534687946428581503 : Rat) / 3200000000000000000000), D0 := ((8750534687946428581503 : Rat) / 3200000000000000000000), D1 := ((2934614367946428581503 : Rat) / 3200000000000000000000), D2 := ((565142687946428581503 : Rat) / 3200000000000000000000), D3 := ((53486090732142858483 : Rat) / 640000000000000000000), D4 := ((613845899196427252561 : Rat) / 12800000000000000000000), LB := ((991319180229877 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8750534687946428581503 : Rat) / 3200000000000000000000), R := ((35006671471339285754697 : Rat) / 12800000000000000000000), D0 := ((35006671471339285754697 : Rat) / 12800000000000000000000), D1 := ((11742990191339285754697 : Rat) / 12800000000000000000000), D2 := ((2265103471339285754697 : Rat) / 12800000000000000000000), D3 := ((214850906839285719669 : Rat) / 2560000000000000000000), D4 := ((152328294910713955969 : Rat) / 3200000000000000000000), LB := ((2065644779262743 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35006671471339285754697 : Rat) / 12800000000000000000000), R := ((17505602095446428591691 : Rat) / 6400000000000000000000), D0 := ((17505602095446428591691 : Rat) / 6400000000000000000000), D1 := ((5873761455446428591691 : Rat) / 6400000000000000000000), D2 := ((1134818095446428591691 : Rat) / 6400000000000000000000), D3 := ((107878725375000002703 : Rat) / 1280000000000000000000), D4 := ((604780460089284395191 : Rat) / 12800000000000000000000), LB := ((3362961799268649 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17505602095446428591691 : Rat) / 6400000000000000000000), R := ((35015736910446428612067 : Rat) / 12800000000000000000000), D0 := ((35015736910446428612067 : Rat) / 12800000000000000000000), D1 := ((11752055630446428612067 : Rat) / 12800000000000000000000), D2 := ((2274168910446428612067 : Rat) / 12800000000000000000000), D3 := ((216663994660714291143 : Rat) / 2560000000000000000000), D4 := ((300123870267856483253 : Rat) / 6400000000000000000000), LB := ((2652088368854111 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35015736910446428612067 : Rat) / 12800000000000000000000), R := ((2188766851875000002547 : Rat) / 800000000000000000000), D0 := ((2188766851875000002547 : Rat) / 800000000000000000000), D1 := ((734786771875000002547 : Rat) / 800000000000000000000), D2 := ((142418851875000002547 : Rat) / 800000000000000000000), D3 := ((2719631732142857211 : Rat) / 32000000000000000000), D4 := ((595715020982141537821 : Rat) / 12800000000000000000000), LB := ((3998320835622571 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2188766851875000002547 : Rat) / 800000000000000000000), R := ((35024802349553571469437 : Rat) / 12800000000000000000000), D0 := ((35024802349553571469437 : Rat) / 12800000000000000000000), D1 := ((11761121069553571469437 : Rat) / 12800000000000000000000), D2 := ((2283234349553571469437 : Rat) / 12800000000000000000000), D3 := ((218477082482142862617 : Rat) / 2560000000000000000000), D4 := ((36948893839285631821 : Rat) / 800000000000000000000), LB := ((1404684896488817 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35024802349553571469437 : Rat) / 12800000000000000000000), R := ((17514667534553571449061 : Rat) / 6400000000000000000000), D0 := ((17514667534553571449061 : Rat) / 6400000000000000000000), D1 := ((5882826894553571449061 : Rat) / 6400000000000000000000), D2 := ((1143883534553571449061 : Rat) / 6400000000000000000000), D3 := ((109691813196428574177 : Rat) / 1280000000000000000000), D4 := ((586649581874998680451 : Rat) / 12800000000000000000000), LB := ((1086481208329923 : Rat) / 6250000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17514667534553571449061 : Rat) / 6400000000000000000000), R := ((35033867788660714326807 : Rat) / 12800000000000000000000), D0 := ((35033867788660714326807 : Rat) / 12800000000000000000000), D1 := ((11770186508660714326807 : Rat) / 12800000000000000000000), D2 := ((2292299788660714326807 : Rat) / 12800000000000000000000), D3 := ((220290170303571434091 : Rat) / 2560000000000000000000), D4 := ((291058431160713625883 : Rat) / 6400000000000000000000), LB := ((1572801722533601 : Rat) / 20000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35033867788660714326807 : Rat) / 12800000000000000000000), R := ((70072268296875000082299 : Rat) / 25600000000000000000000), D0 := ((70072268296875000082299 : Rat) / 25600000000000000000000), D1 := ((23544905736875000082299 : Rat) / 25600000000000000000000), D2 := ((4589132296875000082299 : Rat) / 25600000000000000000000), D3 := ((441486884517857153919 : Rat) / 5120000000000000000000), D4 := ((577584142767855823081 : Rat) / 12800000000000000000000), LB := ((6060913976602689 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70072268296875000082299 : Rat) / 25600000000000000000000), R := ((8759600127053571438873 : Rat) / 3200000000000000000000), D0 := ((8759600127053571438873 : Rat) / 3200000000000000000000), D1 := ((2943679807053571438873 : Rat) / 3200000000000000000000), D2 := ((574208127053571438873 : Rat) / 3200000000000000000000), D3 := ((55299178553571429957 : Rat) / 640000000000000000000), D4 := ((1150635565982140217477 : Rat) / 25600000000000000000000), LB := ((177578827449381 : Rat) / 312500000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8759600127053571438873 : Rat) / 3200000000000000000000), R := ((70081333735982142939669 : Rat) / 25600000000000000000000), D0 := ((70081333735982142939669 : Rat) / 25600000000000000000000), D1 := ((23553971175982142939669 : Rat) / 25600000000000000000000), D2 := ((4598197735982142939669 : Rat) / 25600000000000000000000), D3 := ((443299972339285725393 : Rat) / 5120000000000000000000), D4 := ((143262855803571098599 : Rat) / 3200000000000000000000), LB := ((1333657715374137 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70081333735982142939669 : Rat) / 25600000000000000000000), R := ((35042933227767857184177 : Rat) / 12800000000000000000000), D0 := ((35042933227767857184177 : Rat) / 12800000000000000000000), D1 := ((11779251947767857184177 : Rat) / 12800000000000000000000), D2 := ((2301365227767857184177 : Rat) / 12800000000000000000000), D3 := ((44420651625000001113 : Rat) / 512000000000000000000), D4 := ((1141570126874997360107 : Rat) / 25600000000000000000000), LB := ((5017388201480899 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35042933227767857184177 : Rat) / 12800000000000000000000), R := ((70090399175089285797039 : Rat) / 25600000000000000000000), D0 := ((70090399175089285797039 : Rat) / 25600000000000000000000), D1 := ((23563036615089285797039 : Rat) / 25600000000000000000000), D2 := ((4607263175089285797039 : Rat) / 25600000000000000000000), D3 := ((445113060160714296867 : Rat) / 5120000000000000000000), D4 := ((568518703660712965711 : Rat) / 12800000000000000000000), LB := ((47309458935301807 : Rat) / 100000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70090399175089285797039 : Rat) / 25600000000000000000000), R := ((17523732973660714306431 : Rat) / 6400000000000000000000), D0 := ((17523732973660714306431 : Rat) / 6400000000000000000000), D1 := ((5891892333660714306431 : Rat) / 6400000000000000000000), D2 := ((1152948973660714306431 : Rat) / 6400000000000000000000), D3 := ((111504901017857145651 : Rat) / 1280000000000000000000), D4 := ((1132504687767854502737 : Rat) / 25600000000000000000000), LB := ((1398580526621937 : Rat) / 3125000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17523732973660714306431 : Rat) / 6400000000000000000000), R := ((70099464614196428654409 : Rat) / 25600000000000000000000), D0 := ((70099464614196428654409 : Rat) / 25600000000000000000000), D1 := ((23572102054196428654409 : Rat) / 25600000000000000000000), D2 := ((4616328614196428654409 : Rat) / 25600000000000000000000), D3 := ((446926147982142868341 : Rat) / 5120000000000000000000), D4 := ((281992992053570768513 : Rat) / 6400000000000000000000), LB := ((425107970981331 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70099464614196428654409 : Rat) / 25600000000000000000000), R := ((35051998666875000041547 : Rat) / 12800000000000000000000), D0 := ((35051998666875000041547 : Rat) / 12800000000000000000000), D1 := ((11788317386875000041547 : Rat) / 12800000000000000000000), D2 := ((2310430666875000041547 : Rat) / 12800000000000000000000), D3 := ((223916345946428577039 : Rat) / 2560000000000000000000), D4 := ((1123439248660711645367 : Rat) / 25600000000000000000000), LB := ((2028985260305871 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35051998666875000041547 : Rat) / 12800000000000000000000), R := ((70108530053303571511779 : Rat) / 25600000000000000000000), D0 := ((70108530053303571511779 : Rat) / 25600000000000000000000), D1 := ((23581167493303571511779 : Rat) / 25600000000000000000000), D2 := ((4625394053303571511779 : Rat) / 25600000000000000000000), D3 := ((89747847160714287963 : Rat) / 1024000000000000000000), D4 := ((559453264553570108341 : Rat) / 12800000000000000000000), LB := ((19481455627989863 : Rat) / 50000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70108530053303571511779 : Rat) / 25600000000000000000000), R := ((4382066423303571433779 : Rat) / 1600000000000000000000), D0 := ((4382066423303571433779 : Rat) / 1600000000000000000000), D1 := ((1474106263303571433779 : Rat) / 1600000000000000000000), D2 := ((289370423303571433779 : Rat) / 1600000000000000000000), D3 := ((28102861232142857847 : Rat) / 320000000000000000000), D4 := ((1114373809553568787997 : Rat) / 25600000000000000000000), LB := ((1883102511542889 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4382066423303571433779 : Rat) / 1600000000000000000000), R := ((70117595492410714369149 : Rat) / 25600000000000000000000), D0 := ((70117595492410714369149 : Rat) / 25600000000000000000000), D1 := ((23590232932410714369149 : Rat) / 25600000000000000000000), D2 := ((4634459492410714369149 : Rat) / 25600000000000000000000), D3 := ((450552323625000011289 : Rat) / 5120000000000000000000), D4 := ((69365068124999834957 : Rat) / 1600000000000000000000), LB := ((2292423898871479 : Rat) / 6250000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70117595492410714369149 : Rat) / 25600000000000000000000), R := ((35061064105982142898917 : Rat) / 12800000000000000000000), D0 := ((35061064105982142898917 : Rat) / 12800000000000000000000), D1 := ((11797382825982142898917 : Rat) / 12800000000000000000000), D2 := ((2319496105982142898917 : Rat) / 12800000000000000000000), D3 := ((225729433767857148513 : Rat) / 2560000000000000000000), D4 := ((1105308370446425930627 : Rat) / 25600000000000000000000), LB := ((360147935994537 : Rat) / 1000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35061064105982142898917 : Rat) / 12800000000000000000000), R := ((70126660931517857226519 : Rat) / 25600000000000000000000), D0 := ((70126660931517857226519 : Rat) / 25600000000000000000000), D1 := ((23599298371517857226519 : Rat) / 25600000000000000000000), D2 := ((4643524931517857226519 : Rat) / 25600000000000000000000), D3 := ((452365411446428582763 : Rat) / 5120000000000000000000), D4 := ((550387825446427250971 : Rat) / 12800000000000000000000), LB := ((17835897896018027 : Rat) / 50000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70126660931517857226519 : Rat) / 25600000000000000000000), R := ((17532798412767857163801 : Rat) / 6400000000000000000000), D0 := ((17532798412767857163801 : Rat) / 6400000000000000000000), D1 := ((5900957772767857163801 : Rat) / 6400000000000000000000), D2 := ((1162014412767857163801 : Rat) / 6400000000000000000000), D3 := ((906543910714285737 : Rat) / 10240000000000000000), D4 := ((1096242931339283073257 : Rat) / 25600000000000000000000), LB := ((3565152727497689 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17532798412767857163801 : Rat) / 6400000000000000000000), R := ((70135726370625000083889 : Rat) / 25600000000000000000000), D0 := ((70135726370625000083889 : Rat) / 25600000000000000000000), D1 := ((23608363810625000083889 : Rat) / 25600000000000000000000), D2 := ((4652590370625000083889 : Rat) / 25600000000000000000000), D3 := ((454178499267857154237 : Rat) / 5120000000000000000000), D4 := ((272927552946427911143 : Rat) / 6400000000000000000000), LB := ((898893829181513 : Rat) / 2500000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70135726370625000083889 : Rat) / 25600000000000000000000), R := ((35070129545089285756287 : Rat) / 12800000000000000000000), D0 := ((35070129545089285756287 : Rat) / 12800000000000000000000), D1 := ((11806448265089285756287 : Rat) / 12800000000000000000000), D2 := ((2328561545089285756287 : Rat) / 12800000000000000000000), D3 := ((227542521589285719987 : Rat) / 2560000000000000000000), D4 := ((1087177492232140215887 : Rat) / 25600000000000000000000), LB := ((36586265795696127 : Rat) / 100000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35070129545089285756287 : Rat) / 12800000000000000000000), R := ((70144791809732142941259 : Rat) / 25600000000000000000000), D0 := ((70144791809732142941259 : Rat) / 25600000000000000000000), D1 := ((23617429249732142941259 : Rat) / 25600000000000000000000), D2 := ((4661655809732142941259 : Rat) / 25600000000000000000000), D3 := ((455991587089285725711 : Rat) / 5120000000000000000000), D4 := ((541322386339284393601 : Rat) / 12800000000000000000000), LB := ((3754488510902543 : Rat) / 10000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70144791809732142941259 : Rat) / 25600000000000000000000), R := ((8768665566160714296243 : Rat) / 3200000000000000000000), D0 := ((8768665566160714296243 : Rat) / 3200000000000000000000), D1 := ((2952745246160714296243 : Rat) / 3200000000000000000000), D2 := ((583273566160714296243 : Rat) / 3200000000000000000000), D3 := ((57112266375000001431 : Rat) / 640000000000000000000), D4 := ((1078112053124997358517 : Rat) / 25600000000000000000000), LB := ((9708364775370959 : Rat) / 25000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8768665566160714296243 : Rat) / 3200000000000000000000), R := ((70153857248839285798629 : Rat) / 25600000000000000000000), D0 := ((70153857248839285798629 : Rat) / 25600000000000000000000), D1 := ((23626494688839285798629 : Rat) / 25600000000000000000000), D2 := ((4670721248839285798629 : Rat) / 25600000000000000000000), D3 := ((91560934982142859437 : Rat) / 1024000000000000000000), D4 := ((134197416696428241229 : Rat) / 3200000000000000000000), LB := ((2022693212219151 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70153857248839285798629 : Rat) / 25600000000000000000000), R := ((35079194984196428613657 : Rat) / 12800000000000000000000), D0 := ((35079194984196428613657 : Rat) / 12800000000000000000000), D1 := ((11815513704196428613657 : Rat) / 12800000000000000000000), D2 := ((2337626984196428613657 : Rat) / 12800000000000000000000), D3 := ((229355609410714291461 : Rat) / 2560000000000000000000), D4 := ((1069046614017854501147 : Rat) / 25600000000000000000000), LB := ((1696320237141391 : Rat) / 4000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35079194984196428613657 : Rat) / 12800000000000000000000), R := ((70162922687946428655999 : Rat) / 25600000000000000000000), D0 := ((70162922687946428655999 : Rat) / 25600000000000000000000), D1 := ((23635560127946428655999 : Rat) / 25600000000000000000000), D2 := ((4679786687946428655999 : Rat) / 25600000000000000000000), D3 := ((459617762732142868659 : Rat) / 5120000000000000000000), D4 := ((532256947232141536231 : Rat) / 12800000000000000000000), LB := ((22348909457903243 : Rat) / 50000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70162922687946428655999 : Rat) / 25600000000000000000000), R := ((17541863851875000021171 : Rat) / 6400000000000000000000), D0 := ((17541863851875000021171 : Rat) / 6400000000000000000000), D1 := ((5910023211875000021171 : Rat) / 6400000000000000000000), D2 := ((1171079851875000021171 : Rat) / 6400000000000000000000), D3 := ((115131076660714288599 : Rat) / 1280000000000000000000), D4 := ((1059981174910711643777 : Rat) / 25600000000000000000000), LB := ((11831316950096371 : Rat) / 25000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17541863851875000021171 : Rat) / 6400000000000000000000), R := ((70171988127053571513369 : Rat) / 25600000000000000000000), D0 := ((70171988127053571513369 : Rat) / 25600000000000000000000), D1 := ((23644625567053571513369 : Rat) / 25600000000000000000000), D2 := ((4688852127053571513369 : Rat) / 25600000000000000000000), D3 := ((461430850553571440133 : Rat) / 5120000000000000000000), D4 := ((263862113839285053773 : Rat) / 6400000000000000000000), LB := ((125730868702989 : Rat) / 250000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70171988127053571513369 : Rat) / 25600000000000000000000), R := ((35088260423303571471027 : Rat) / 12800000000000000000000), D0 := ((35088260423303571471027 : Rat) / 12800000000000000000000), D1 := ((11824579143303571471027 : Rat) / 12800000000000000000000), D2 := ((2346692423303571471027 : Rat) / 12800000000000000000000), D3 := ((46233739446428572587 : Rat) / 512000000000000000000), D4 := ((1050915735803568786407 : Rat) / 25600000000000000000000), LB := ((2680054182223057 : Rat) / 5000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35088260423303571471027 : Rat) / 12800000000000000000000), R := ((70181053566160714370739 : Rat) / 25600000000000000000000), D0 := ((70181053566160714370739 : Rat) / 25600000000000000000000), D1 := ((23653691006160714370739 : Rat) / 25600000000000000000000), D2 := ((4697917566160714370739 : Rat) / 25600000000000000000000), D3 := ((463243938375000011607 : Rat) / 5120000000000000000000), D4 := ((523191508124998678861 : Rat) / 12800000000000000000000), LB := ((1145070665127923 : Rat) / 2000000000000000000) },
  { w1 := ((8101058823017069 : Rat) / 10000000000000000), w2 := ((10375980494313661 : Rat) / 250000000000000000), w3 := ((17015423113646483 : Rat) / 100000000000000000), w4 := ((7284535839301323 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132548503660714285767 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70181053566160714370739 : Rat) / 25600000000000000000000), R := ((34270305803571428613 : Rat) / 12500000000000000000), D0 := ((34270305803571428613 : Rat) / 12500000000000000000), D1 := ((11551867053571428613 : Rat) / 12500000000000000000), D2 := ((2296118303571428613 : Rat) / 12500000000000000000), D3 := ((906543910714285737 : Rat) / 10000000000000000000), D4 := ((1041850296696425929037 : Rat) / 25600000000000000000000), LB := ((1531294626710561 : Rat) / 2500000000000000000) }
]

def block388RightChunk001L : Rat := ((3207515409 : Rat) / 1280000000)
def block388RightChunk001R : Rat := ((34270305803571428613 : Rat) / 12500000000000000000)

def block388RightChunk001Certificate : Bool :=
  allBoxesValid block388RightChunk001 &&
  coversFromBool block388RightChunk001 block388RightChunk001L block388RightChunk001R

theorem block388RightChunk001Certificate_eq_true :
    block388RightChunk001Certificate = true := by
  native_decide

def block388RightChainCertificate : Bool :=
  decide (
    block388RightL = ((87071448660714285881 : Rat) / 50000000000000000000) /\
    ((3207515409 : Rat) / 1280000000) = ((3207515409 : Rat) / 1280000000) /\
    ((34270305803571428613 : Rat) / 12500000000000000000) = block388RightR)

theorem block388RightChainCertificate_eq_true :
    block388RightChainCertificate = true := by
  native_decide

def block388LeftBoxCount : Nat := boxCount block388LeftBoxes
def block388RightBoxCount : Nat := 156

def block388_rational_certificate : Prop :=
    block388LeftCertificate = true /\
    block388RightChainCertificate = true /\
    block388RightChunk000Certificate = true /\
    block388RightChunk001Certificate = true

theorem block388_rational_certificate_proof :
    block388_rational_certificate := by
  exact ⟨block388LeftCertificate_eq_true, block388RightChainCertificate_eq_true, block388RightChunk000Certificate_eq_true, block388RightChunk001Certificate_eq_true⟩

end Block388
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block388

open Set

def block388W1 : Rat := ((8101058823017069 : Rat) / 10000000000000000)
def block388W2 : Rat := ((10375980494313661 : Rat) / 250000000000000000)
def block388W3 : Rat := ((17015423113646483 : Rat) / 100000000000000000)
def block388W4 : Rat := ((7284535839301323 : Rat) / 50000000000000000)
def block388S1 : Rat := ((18174751 : Rat) / 10000000)
def block388S2 : Rat := ((511587 : Rat) / 200000)
def block388S3 : Rat := ((132548503660714285767 : Rat) / 50000000000000000000)
def block388S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block388V (y : ℝ) : ℝ :=
  ratPotential block388W1 block388W2 block388W3 block388W4 block388S1 block388S2 block388S3 block388S4 y

def block388LeftParamsCertificate : Bool :=
  allBoxesSameParams block388LeftBoxes block388W1 block388W2 block388W3 block388W4 block388S1 block388S2 block388S3 block388S4

theorem block388LeftParamsCertificate_eq_true :
    block388LeftParamsCertificate = true := by
  native_decide

theorem block388_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block388LeftL : ℝ) (block388LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block388S1 : ℝ))
    (hy2ne : y ≠ (block388S2 : ℝ))
    (hy3ne : y ≠ (block388S3 : ℝ))
    (hy4ne : y ≠ (block388S4 : ℝ)) :
    0 < block388V y := by
  have hcert := block388LeftCertificate_eq_true
  unfold block388LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block388LeftBoxes) (lo := block388LeftL) (hi := block388LeftR)
    (w1 := block388W1) (w2 := block388W2) (w3 := block388W3) (w4 := block388W4)
    (s1 := block388S1) (s2 := block388S2) (s3 := block388S3) (s4 := block388S4)
    hboxes hcover block388LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block388RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block388RightChunk000 block388W1 block388W2 block388W3 block388W4 block388S1 block388S2 block388S3 block388S4

theorem block388RightChunk000ParamsCertificate_eq_true :
    block388RightChunk000ParamsCertificate = true := by
  native_decide

theorem block388_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block388RightChunk000L : ℝ) (block388RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block388S1 : ℝ))
    (hy2ne : y ≠ (block388S2 : ℝ))
    (hy3ne : y ≠ (block388S3 : ℝ))
    (hy4ne : y ≠ (block388S4 : ℝ)) :
    0 < block388V y := by
  have hcert := block388RightChunk000Certificate_eq_true
  unfold block388RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block388RightChunk000) (lo := block388RightChunk000L) (hi := block388RightChunk000R)
    (w1 := block388W1) (w2 := block388W2) (w3 := block388W3) (w4 := block388W4)
    (s1 := block388S1) (s2 := block388S2) (s3 := block388S3) (s4 := block388S4)
    hboxes hcover block388RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block388RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block388RightChunk001 block388W1 block388W2 block388W3 block388W4 block388S1 block388S2 block388S3 block388S4

theorem block388RightChunk001ParamsCertificate_eq_true :
    block388RightChunk001ParamsCertificate = true := by
  native_decide

theorem block388_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block388RightChunk001L : ℝ) (block388RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block388S1 : ℝ))
    (hy2ne : y ≠ (block388S2 : ℝ))
    (hy3ne : y ≠ (block388S3 : ℝ))
    (hy4ne : y ≠ (block388S4 : ℝ)) :
    0 < block388V y := by
  have hcert := block388RightChunk001Certificate_eq_true
  unfold block388RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block388RightChunk001) (lo := block388RightChunk001L) (hi := block388RightChunk001R)
    (w1 := block388W1) (w2 := block388W2) (w3 := block388W3) (w4 := block388W4)
    (s1 := block388S1) (s2 := block388S2) (s3 := block388S3) (s4 := block388S4)
    hboxes hcover block388RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block388_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block388RightL : ℝ) (block388RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block388S1 : ℝ))
    (hy2ne : y ≠ (block388S2 : ℝ))
    (hy3ne : y ≠ (block388S3 : ℝ))
    (hy4ne : y ≠ (block388S4 : ℝ)) :
    0 < block388V y := by
  by_cases h0 : y ≤ (block388RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block388RightChunk000L : ℝ) (block388RightChunk000R : ℝ) := by
      have hL : (block388RightChunk000L : ℝ) = (block388RightL : ℝ) := by
        norm_num [block388RightChunk000L, block388RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block388_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block388RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block388RightChunk001L : ℝ) = (block388RightChunk000R : ℝ) := by
      norm_num [block388RightChunk001L, block388RightChunk000R]
    have hR : (block388RightChunk001R : ℝ) = (block388RightR : ℝ) := by
      norm_num [block388RightChunk001R, block388RightR]
    have hyc : y ∈ Icc (block388RightChunk001L : ℝ) (block388RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block388_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block388_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block388LeftL : ℝ) (block388LeftR : ℝ) →
    y ≠ 0 → y ≠ (block388S1 : ℝ) → y ≠ (block388S2 : ℝ) →
    y ≠ (block388S3 : ℝ) → y ≠ (block388S4 : ℝ) → 0 < block388V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block388RightL : ℝ) (block388RightR : ℝ) →
    y ≠ 0 → y ≠ (block388S1 : ℝ) → y ≠ (block388S2 : ℝ) →
    y ≠ (block388S3 : ℝ) → y ≠ (block388S4 : ℝ) → 0 < block388V y)

theorem block388_reallog_certificate_proof :
    block388_reallog_certificate := by
  exact ⟨block388_left_V_pos, block388_right_V_pos⟩

end Block388
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block388.block388V
#check Erdos1038Lean.M1817475.Block388.block388_left_V_pos
#check Erdos1038Lean.M1817475.Block388.block388_right_V_pos
#check Erdos1038Lean.M1817475.Block388.block388_reallog_certificate_proof
