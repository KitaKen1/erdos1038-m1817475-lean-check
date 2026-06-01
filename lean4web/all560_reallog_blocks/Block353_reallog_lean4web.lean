/-
Self-contained Lean4Web paste file.
Block 353 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block353

def block353LeftL : Rat := ((18706779017857142933 : Rat) / 25000000000000000000)
def block353LeftR : Rat := ((37423332589285714437 : Rat) / 50000000000000000000)
def block353RightL : Rat := ((43706779017857142933 : Rat) / 25000000000000000000)
def block353RightR : Rat := ((137423332589285714437 : Rat) / 50000000000000000000)

def block353LeftBoxes : List RatBox := [
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18706779017857142933 : Rat) / 25000000000000000000), R := ((37423332589285714437 : Rat) / 50000000000000000000), D0 := ((37423332589285714437 : Rat) / 50000000000000000000), D1 := ((26730098482142857067 : Rat) / 25000000000000000000), D2 := ((45241595982142857067 : Rat) / 25000000000000000000), D3 := ((95819164374999999871 : Rat) / 50000000000000000000), D4 := ((25301237098214284433 : Rat) / 12500000000000000000), LB := ((6219026503201663 : Rat) / 1000000000000000000) }
]

def block353LeftCertificate : Bool :=
  allBoxesValid block353LeftBoxes &&
  coversFromBool block353LeftBoxes block353LeftL block353LeftR

theorem block353LeftCertificate_eq_true :
    block353LeftCertificate = true := by
  native_decide

def block353RightChunk000 : List RatBox := [
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43706779017857142933 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1730098482142857067 : Rat) / 25000000000000000000), D2 := ((20241595982142857067 : Rat) / 25000000000000000000), D3 := ((45819164374999999871 : Rat) / 50000000000000000000), D4 := ((12801237098214284433 : Rat) / 12500000000000000000), LB := ((4565699256352539 : Rat) / 2500000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42358967410714285737 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((3140763429989381 : Rat) / 20000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23847469910714285737 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((5084737432470101 : Rat) / 50000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19219595535714285737 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((6567608051179817 : Rat) / 100000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16905658348214285737 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((576400025893601 : Rat) / 62500000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14591721160714285737 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((265265947852681 : Rat) / 25000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13434752566964285737 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((2991018440610843 : Rat) / 200000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12856268270089285737 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((35616098175867 : Rat) / 5000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12277783973214285737 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((4655276161223687 : Rat) / 12500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11699299676339285737 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((552243778261019 : Rat) / 100000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11410057527901785737 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((3104772925369259 : Rat) / 1000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11120815379464285737 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((5076346602125581 : Rat) / 5000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10831573231026785737 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((4550263987018133 : Rat) / 1000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10686952156808035737 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((37925056097982413 : Rat) / 10000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10542331082589285737 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((31281505154845957 : Rat) / 10000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10397710008370535737 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((2559949767656139 : Rat) / 1000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10253088934151785737 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((32669760830347 : Rat) / 15625000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10108467859933035737 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((8620446135516463 : Rat) / 5000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9963846785714285737 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((3657688834993733 : Rat) / 2500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9819225711495535737 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((104925081107341 : Rat) / 80000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9674604637276785737 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((318403735398029 : Rat) / 250000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9529983563058035737 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((3384132908254081 : Rat) / 2500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9385362488839285737 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((15565094976718319 : Rat) / 10000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9240741414620535737 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((18874777818815303 : Rat) / 10000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9096120340401785737 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((735118399427543 : Rat) / 312500000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8951499266183035737 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((14788187267614217 : Rat) / 5000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8806878191964285737 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((18551870011719457 : Rat) / 5000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8662257117745535737 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((2309257981499127 : Rat) / 500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8517636043526785737 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((889033778053161 : Rat) / 1250000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8228393895089285737 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((3424972135051163 : Rat) / 1000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7939151746651785737 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((433356374892507 : Rat) / 62500000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7649909598214285737 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((1662179315995771 : Rat) / 1000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7071425301339285737 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((14204593595932069 : Rat) / 1000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6492941004464285737 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((7602654267646683 : Rat) / 500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516922972410714285737 : Rat) / 200000000000000000000), D0 := ((516922972410714285737 : Rat) / 200000000000000000000), D1 := ((153427952410714285737 : Rat) / 200000000000000000000), D2 := ((5335972410714285737 : Rat) / 200000000000000000000), D3 := ((5335972410714285737 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((1219361427574471 : Rat) / 125000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516922972410714285737 : Rat) / 200000000000000000000), R := ((1039181917232142857211 : Rat) / 400000000000000000000), D0 := ((1039181917232142857211 : Rat) / 400000000000000000000), D1 := ((312191877232142857211 : Rat) / 400000000000000000000), D2 := ((16007917232142857211 : Rat) / 400000000000000000000), D3 := ((16007917232142857211 : Rat) / 200000000000000000000), D4 := ((7510210660714281731 : Rat) / 40000000000000000000), LB := ((31244938845564507 : Rat) / 1000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1039181917232142857211 : Rat) / 400000000000000000000), R := ((261129472410714285737 : Rat) / 100000000000000000000), D0 := ((261129472410714285737 : Rat) / 100000000000000000000), D1 := ((79381962410714285737 : Rat) / 100000000000000000000), D2 := ((5335972410714285737 : Rat) / 100000000000000000000), D3 := ((5335972410714285737 : Rat) / 80000000000000000000), D4 := ((69766134196428531573 : Rat) / 400000000000000000000), LB := ((3466710280243199 : Rat) / 100000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261129472410714285737 : Rat) / 100000000000000000000), R := ((527594917232142857211 : Rat) / 200000000000000000000), D0 := ((527594917232142857211 : Rat) / 200000000000000000000), D1 := ((164099897232142857211 : Rat) / 200000000000000000000), D2 := ((16007917232142857211 : Rat) / 200000000000000000000), D3 := ((5335972410714285737 : Rat) / 100000000000000000000), D4 := ((16107540446428561459 : Rat) / 100000000000000000000), LB := ((198592693223813 : Rat) / 10000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((527594917232142857211 : Rat) / 200000000000000000000), R := ((133232722410714285737 : Rat) / 50000000000000000000), D0 := ((133232722410714285737 : Rat) / 50000000000000000000), D1 := ((42358967410714285737 : Rat) / 50000000000000000000), D2 := ((5335972410714285737 : Rat) / 50000000000000000000), D3 := ((5335972410714285737 : Rat) / 200000000000000000000), D4 := ((26879108482142837181 : Rat) / 200000000000000000000), LB := ((9611342916370869 : Rat) / 100000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133232722410714285737 : Rat) / 50000000000000000000), R := ((1049065429338727679 : Rat) / 390625000000000000), D0 := ((1049065429338727679 : Rat) / 390625000000000000), D1 := ((339114218401227679 : Rat) / 390625000000000000), D2 := ((49872069963727679 : Rat) / 390625000000000000), D3 := ((41906101785714287 : Rat) / 2000000000000000000), D4 := ((5385784017857137861 : Rat) / 50000000000000000000), LB := ((12457530275754647 : Rat) / 100000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1049065429338727679 : Rat) / 390625000000000000), R := ((135328027500000000087 : Rat) / 50000000000000000000), D0 := ((135328027500000000087 : Rat) / 50000000000000000000), D1 := ((44454272500000000087 : Rat) / 50000000000000000000), D2 := ((7431277500000000087 : Rat) / 50000000000000000000), D3 := ((41906101785714287 : Rat) / 1000000000000000000), D4 := ((2169065736607140343 : Rat) / 25000000000000000000), LB := ((7175705769406321 : Rat) / 500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((135328027500000000087 : Rat) / 50000000000000000000), R := ((271703707544642857349 : Rat) / 100000000000000000000), D0 := ((271703707544642857349 : Rat) / 100000000000000000000), D1 := ((89956197544642857349 : Rat) / 100000000000000000000), D2 := ((15910207544642857349 : Rat) / 100000000000000000000), D3 := ((41906101785714287 : Rat) / 800000000000000000), D4 := ((3290478928571423511 : Rat) / 50000000000000000000), LB := ((4023859341449887 : Rat) / 2500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((271703707544642857349 : Rat) / 100000000000000000000), R := ((544455067633928571873 : Rat) / 200000000000000000000), D0 := ((544455067633928571873 : Rat) / 200000000000000000000), D1 := ((180960047633928571873 : Rat) / 200000000000000000000), D2 := ((32868067633928571873 : Rat) / 200000000000000000000), D3 := ((460967119642857157 : Rat) / 8000000000000000000), D4 := ((5533305312499989847 : Rat) / 100000000000000000000), LB := ((1071554575088407 : Rat) / 400000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((544455067633928571873 : Rat) / 200000000000000000000), R := ((1089957787812500000921 : Rat) / 400000000000000000000), D0 := ((1089957787812500000921 : Rat) / 400000000000000000000), D1 := ((362967747812500000921 : Rat) / 400000000000000000000), D2 := ((66783787812500000921 : Rat) / 400000000000000000000), D3 := ((963840341071428601 : Rat) / 16000000000000000000), D4 := ((10018958080357122519 : Rat) / 200000000000000000000), LB := ((1372875519265307 : Rat) / 250000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1089957787812500000921 : Rat) / 400000000000000000000), R := ((68187840022321428631 : Rat) / 25000000000000000000), D0 := ((68187840022321428631 : Rat) / 25000000000000000000), D1 := ((22750962522321428631 : Rat) / 25000000000000000000), D2 := ((4239465022321428631 : Rat) / 25000000000000000000), D3 := ((125718305357142861 : Rat) / 2000000000000000000), D4 := ((18990263616071387863 : Rat) / 400000000000000000000), LB := ((11337862776245877 : Rat) / 5000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((68187840022321428631 : Rat) / 25000000000000000000), R := ((2183058533258928573367 : Rat) / 800000000000000000000), D0 := ((2183058533258928573367 : Rat) / 800000000000000000000), D1 := ((729078453258928573367 : Rat) / 800000000000000000000), D2 := ((136710533258928573367 : Rat) / 800000000000000000000), D3 := ((2053398987500000063 : Rat) / 32000000000000000000), D4 := ((35044162248883849 : Rat) / 781250000000000000), LB := ((2452349379830271 : Rat) / 500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2183058533258928573367 : Rat) / 800000000000000000000), R := ((1092053092901785715271 : Rat) / 400000000000000000000), D0 := ((1092053092901785715271 : Rat) / 400000000000000000000), D1 := ((365063052901785715271 : Rat) / 400000000000000000000), D2 := ((68879092901785715271 : Rat) / 400000000000000000000), D3 := ((41906101785714287 : Rat) / 640000000000000000), D4 := ((34837569598214204201 : Rat) / 800000000000000000000), LB := ((7702660868360467 : Rat) / 2000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1092053092901785715271 : Rat) / 400000000000000000000), R := ((2185153838348214287717 : Rat) / 800000000000000000000), D0 := ((2185153838348214287717 : Rat) / 800000000000000000000), D1 := ((731173758348214287717 : Rat) / 800000000000000000000), D2 := ((138805838348214287717 : Rat) / 800000000000000000000), D3 := ((2137211191071428637 : Rat) / 32000000000000000000), D4 := ((16894958526785673513 : Rat) / 400000000000000000000), LB := ((2988036864452759 : Rat) / 1000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2185153838348214287717 : Rat) / 800000000000000000000), R := ((546550372723214286223 : Rat) / 200000000000000000000), D0 := ((546550372723214286223 : Rat) / 200000000000000000000), D1 := ((183055352723214286223 : Rat) / 200000000000000000000), D2 := ((34963372723214286223 : Rat) / 200000000000000000000), D3 := ((544779323214285731 : Rat) / 8000000000000000000), D4 := ((32742264508928489851 : Rat) / 800000000000000000000), LB := ((23203442567744093 : Rat) / 10000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546550372723214286223 : Rat) / 200000000000000000000), R := ((2187249143437500002067 : Rat) / 800000000000000000000), D0 := ((2187249143437500002067 : Rat) / 800000000000000000000), D1 := ((733269063437500002067 : Rat) / 800000000000000000000), D2 := ((140901143437500002067 : Rat) / 800000000000000000000), D3 := ((2221023394642857211 : Rat) / 32000000000000000000), D4 := ((7923652991071408169 : Rat) / 200000000000000000000), LB := ((18546834141002777 : Rat) / 10000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2187249143437500002067 : Rat) / 800000000000000000000), R := ((1094148397991071429621 : Rat) / 400000000000000000000), D0 := ((1094148397991071429621 : Rat) / 400000000000000000000), D1 := ((367158357991071429621 : Rat) / 400000000000000000000), D2 := ((70974397991071429621 : Rat) / 400000000000000000000), D3 := ((1131464748214285749 : Rat) / 16000000000000000000), D4 := ((30646959419642775501 : Rat) / 800000000000000000000), LB := ((3196966876552243 : Rat) / 2000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094148397991071429621 : Rat) / 400000000000000000000), R := ((2189344448526785716417 : Rat) / 800000000000000000000), D0 := ((2189344448526785716417 : Rat) / 800000000000000000000), D1 := ((735364368526785716417 : Rat) / 800000000000000000000), D2 := ((142996448526785716417 : Rat) / 800000000000000000000), D3 := ((460967119642857157 : Rat) / 6400000000000000000), D4 := ((14799653437499959163 : Rat) / 400000000000000000000), LB := ((3900710955648673 : Rat) / 2500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2189344448526785716417 : Rat) / 800000000000000000000), R := ((273799012633928571699 : Rat) / 100000000000000000000), D0 := ((273799012633928571699 : Rat) / 100000000000000000000), D1 := ((92051502633928571699 : Rat) / 100000000000000000000), D2 := ((18005512633928571699 : Rat) / 100000000000000000000), D3 := ((293342712500000009 : Rat) / 4000000000000000000), D4 := ((28551654330357061151 : Rat) / 800000000000000000000), LB := ((8544300077419 : Rat) / 4882812500000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((273799012633928571699 : Rat) / 100000000000000000000), R := ((2191439753616071430767 : Rat) / 800000000000000000000), D0 := ((2191439753616071430767 : Rat) / 800000000000000000000), D1 := ((737459673616071430767 : Rat) / 800000000000000000000), D2 := ((145091753616071430767 : Rat) / 800000000000000000000), D3 := ((2388647801785714359 : Rat) / 32000000000000000000), D4 := ((3438000223214275497 : Rat) / 100000000000000000000), LB := ((544611005617493 : Rat) / 250000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2191439753616071430767 : Rat) / 800000000000000000000), R := ((1096243703080357143971 : Rat) / 400000000000000000000), D0 := ((1096243703080357143971 : Rat) / 400000000000000000000), D1 := ((369253663080357143971 : Rat) / 400000000000000000000), D2 := ((73069703080357143971 : Rat) / 400000000000000000000), D3 := ((1215276951785714323 : Rat) / 16000000000000000000), D4 := ((26456349241071346801 : Rat) / 800000000000000000000), LB := ((28588003743855173 : Rat) / 10000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1096243703080357143971 : Rat) / 400000000000000000000), R := ((2193535058705357145117 : Rat) / 800000000000000000000), D0 := ((2193535058705357145117 : Rat) / 800000000000000000000), D1 := ((739554978705357145117 : Rat) / 800000000000000000000), D2 := ((147187058705357145117 : Rat) / 800000000000000000000), D3 := ((2472460005357142933 : Rat) / 32000000000000000000), D4 := ((12704348348214244813 : Rat) / 400000000000000000000), LB := ((38055882558107323 : Rat) / 10000000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2193535058705357145117 : Rat) / 800000000000000000000), R := ((548645677812500000573 : Rat) / 200000000000000000000), D0 := ((548645677812500000573 : Rat) / 200000000000000000000), D1 := ((185150657812500000573 : Rat) / 200000000000000000000), D2 := ((37058677812500000573 : Rat) / 200000000000000000000), D3 := ((125718305357142861 : Rat) / 1600000000000000000), D4 := ((24361044151785632451 : Rat) / 800000000000000000000), LB := ((62944868510037 : Rat) / 12500000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((548645677812500000573 : Rat) / 200000000000000000000), R := ((1098339008169642858321 : Rat) / 400000000000000000000), D0 := ((1098339008169642858321 : Rat) / 400000000000000000000), D1 := ((371348968169642858321 : Rat) / 400000000000000000000), D2 := ((75165008169642858321 : Rat) / 400000000000000000000), D3 := ((1299089155357142897 : Rat) / 16000000000000000000), D4 := ((5828347901785693819 : Rat) / 200000000000000000000), LB := ((1027104636748849 : Rat) / 500000000000000000) },
  { w1 := ((2250262504208217 : Rat) / 2500000000000000), w2 := ((4761155216780289 : Rat) / 100000000000000000), w3 := ((3741075219411287 : Rat) / 25000000000000000), w4 := ((692824335890697 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133232722410714285737 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1098339008169642858321 : Rat) / 400000000000000000000), R := ((137423332589285714437 : Rat) / 50000000000000000000), D0 := ((137423332589285714437 : Rat) / 50000000000000000000), D1 := ((46549577589285714437 : Rat) / 50000000000000000000), D2 := ((9526582589285714437 : Rat) / 50000000000000000000), D3 := ((41906101785714287 : Rat) / 500000000000000000), D4 := ((10609043258928530463 : Rat) / 400000000000000000000), LB := ((3102104778418907 : Rat) / 500000000000000000) }
]

def block353RightChunk000L : Rat := ((43706779017857142933 : Rat) / 25000000000000000000)
def block353RightChunk000R : Rat := ((137423332589285714437 : Rat) / 50000000000000000000)

def block353RightChunk000Certificate : Bool :=
  allBoxesValid block353RightChunk000 &&
  coversFromBool block353RightChunk000 block353RightChunk000L block353RightChunk000R

theorem block353RightChunk000Certificate_eq_true :
    block353RightChunk000Certificate = true := by
  native_decide

def block353RightChainCertificate : Bool :=
  decide (
    block353RightL = ((43706779017857142933 : Rat) / 25000000000000000000) /\
    ((137423332589285714437 : Rat) / 50000000000000000000) = block353RightR)

theorem block353RightChainCertificate_eq_true :
    block353RightChainCertificate = true := by
  native_decide

def block353LeftBoxCount : Nat := boxCount block353LeftBoxes
def block353RightBoxCount : Nat := 59

def block353_rational_certificate : Prop :=
    block353LeftCertificate = true /\
    block353RightChainCertificate = true /\
    block353RightChunk000Certificate = true

theorem block353_rational_certificate_proof :
    block353_rational_certificate := by
  exact ⟨block353LeftCertificate_eq_true, block353RightChainCertificate_eq_true, block353RightChunk000Certificate_eq_true⟩

end Block353
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block353

open Set

def block353W1 : Rat := ((2250262504208217 : Rat) / 2500000000000000)
def block353W2 : Rat := ((4761155216780289 : Rat) / 100000000000000000)
def block353W3 : Rat := ((3741075219411287 : Rat) / 25000000000000000)
def block353W4 : Rat := ((692824335890697 : Rat) / 5000000000000000)
def block353S1 : Rat := ((18174751 : Rat) / 10000000)
def block353S2 : Rat := ((511587 : Rat) / 200000)
def block353S3 : Rat := ((133232722410714285737 : Rat) / 50000000000000000000)
def block353S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block353V (y : ℝ) : ℝ :=
  ratPotential block353W1 block353W2 block353W3 block353W4 block353S1 block353S2 block353S3 block353S4 y

def block353LeftParamsCertificate : Bool :=
  allBoxesSameParams block353LeftBoxes block353W1 block353W2 block353W3 block353W4 block353S1 block353S2 block353S3 block353S4

theorem block353LeftParamsCertificate_eq_true :
    block353LeftParamsCertificate = true := by
  native_decide

theorem block353_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block353LeftL : ℝ) (block353LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block353S1 : ℝ))
    (hy2ne : y ≠ (block353S2 : ℝ))
    (hy3ne : y ≠ (block353S3 : ℝ))
    (hy4ne : y ≠ (block353S4 : ℝ)) :
    0 < block353V y := by
  have hcert := block353LeftCertificate_eq_true
  unfold block353LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block353LeftBoxes) (lo := block353LeftL) (hi := block353LeftR)
    (w1 := block353W1) (w2 := block353W2) (w3 := block353W3) (w4 := block353W4)
    (s1 := block353S1) (s2 := block353S2) (s3 := block353S3) (s4 := block353S4)
    hboxes hcover block353LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block353RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block353RightChunk000 block353W1 block353W2 block353W3 block353W4 block353S1 block353S2 block353S3 block353S4

theorem block353RightChunk000ParamsCertificate_eq_true :
    block353RightChunk000ParamsCertificate = true := by
  native_decide

theorem block353_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block353RightChunk000L : ℝ) (block353RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block353S1 : ℝ))
    (hy2ne : y ≠ (block353S2 : ℝ))
    (hy3ne : y ≠ (block353S3 : ℝ))
    (hy4ne : y ≠ (block353S4 : ℝ)) :
    0 < block353V y := by
  have hcert := block353RightChunk000Certificate_eq_true
  unfold block353RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block353RightChunk000) (lo := block353RightChunk000L) (hi := block353RightChunk000R)
    (w1 := block353W1) (w2 := block353W2) (w3 := block353W3) (w4 := block353W4)
    (s1 := block353S1) (s2 := block353S2) (s3 := block353S3) (s4 := block353S4)
    hboxes hcover block353RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block353_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block353RightL : ℝ) (block353RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block353S1 : ℝ))
    (hy2ne : y ≠ (block353S2 : ℝ))
    (hy3ne : y ≠ (block353S3 : ℝ))
    (hy4ne : y ≠ (block353S4 : ℝ)) :
    0 < block353V y := by
  have hL : (block353RightChunk000L : ℝ) = (block353RightL : ℝ) := by
    norm_num [block353RightChunk000L, block353RightL]
  have hR : (block353RightChunk000R : ℝ) = (block353RightR : ℝ) := by
    norm_num [block353RightChunk000R, block353RightR]
  have hyc : y ∈ Icc (block353RightChunk000L : ℝ) (block353RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block353_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block353_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block353LeftL : ℝ) (block353LeftR : ℝ) →
    y ≠ 0 → y ≠ (block353S1 : ℝ) → y ≠ (block353S2 : ℝ) →
    y ≠ (block353S3 : ℝ) → y ≠ (block353S4 : ℝ) → 0 < block353V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block353RightL : ℝ) (block353RightR : ℝ) →
    y ≠ 0 → y ≠ (block353S1 : ℝ) → y ≠ (block353S2 : ℝ) →
    y ≠ (block353S3 : ℝ) → y ≠ (block353S4 : ℝ) → 0 < block353V y)

theorem block353_reallog_certificate_proof :
    block353_reallog_certificate := by
  exact ⟨block353_left_V_pos, block353_right_V_pos⟩

end Block353
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block353.block353V
#check Erdos1038Lean.M1817475.Block353.block353_left_V_pos
#check Erdos1038Lean.M1817475.Block353.block353_right_V_pos
#check Erdos1038Lean.M1817475.Block353.block353_reallog_certificate_proof
