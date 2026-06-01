/-
Self-contained Lean4Web paste file.
Block 367 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block367

def block367LeftL : Rat := ((2329794642857142867 : Rat) / 3125000000000000000)
def block367LeftR : Rat := ((37286488839285714443 : Rat) / 50000000000000000000)
def block367RightL : Rat := ((5454794642857142867 : Rat) / 3125000000000000000)
def block367RightR : Rat := ((137286488839285714443 : Rat) / 50000000000000000000)

def block367LeftBoxes : List RatBox := [
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2329794642857142867 : Rat) / 3125000000000000000), R := ((37286488839285714443 : Rat) / 50000000000000000000), D0 := ((37286488839285714443 : Rat) / 50000000000000000000), D1 := ((3349815044642857133 : Rat) / 3125000000000000000), D2 := ((5663752232142857133 : Rat) / 3125000000000000000), D3 := ((95682320624999999877 : Rat) / 50000000000000000000), D4 := ((50670896071428568863 : Rat) / 25000000000000000000), LB := ((6177672293828831 : Rat) / 1000000000000000000) }
]

def block367LeftCertificate : Bool :=
  allBoxesValid block367LeftBoxes &&
  coversFromBool block367LeftBoxes block367LeftL block367LeftR

theorem block367LeftCertificate_eq_true :
    block367LeftCertificate = true := by
  native_decide

def block367RightChunk000 : List RatBox := [
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((5454794642857142867 : Rat) / 3125000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((224815044642857133 : Rat) / 3125000000000000000), D2 := ((2538752232142857133 : Rat) / 3125000000000000000), D3 := ((45682320624999999877 : Rat) / 50000000000000000000), D4 := ((25670896071428568863 : Rat) / 25000000000000000000), LB := ((17199850634207667 : Rat) / 10000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42085279910714285749 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((205727486665547 : Rat) / 1562500000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23573782410714285749 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((8586997579444233 : Rat) / 100000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18945908035714285749 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((841688790803419 : Rat) / 15625000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16631970848214285749 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((6692122341776519 : Rat) / 10000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14318033660714285749 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((4230842094675363 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13161065066964285749 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((9733710438718873 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12582580770089285749 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((2767655490235277 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12004096473214285749 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((235960085280971 : Rat) / 31250000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11714854324776785749 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((2481905385041727 : Rat) / 500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11425612176339285749 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((26822214974895897 : Rat) / 10000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11136370027901785749 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((718938954882703 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10847127879464285749 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((4284231258671001 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10702506805245535749 : Rat) / 50000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((1789664470948027 : Rat) / 500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10557885731026785749 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((14821412449511767 : Rat) / 5000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10413264656808035749 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((24415496080896493 : Rat) / 10000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10268643582589285749 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((5034410948347931 : Rat) / 2500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10124022508370535749 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((16837546185413943 : Rat) / 10000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9979401434151785749 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((58182463843649 : Rat) / 40000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9834780359933035749 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((13294625413904637 : Rat) / 10000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9690159285714285749 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((13119964245971727 : Rat) / 10000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9545538211495535749 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((702996812036033 : Rat) / 500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9400917137276785749 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((1009756390406933 : Rat) / 625000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9256296063058035749 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((972683933340393 : Rat) / 500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9111674988839285749 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((24002002893842023 : Rat) / 10000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((8967053914620535749 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((14927540002955403 : Rat) / 5000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8822432840401785749 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((3707222880049099 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8677811766183035749 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((914377003227429 : Rat) / 200000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8533190691964285749 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((3440555352689917 : Rat) / 5000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8243948543526785749 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((3235960399756571 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7954706395089285749 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((1623492070015671 : Rat) / 250000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7665464246651785749 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((1056044658009661 : Rat) / 100000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7376222098214285749 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((3042581945335257 : Rat) / 500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6797737801339285749 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1981630629940581 : Rat) / 100000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6219253504464285749 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((5624878969867443 : Rat) / 250000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516649284910714285749 : Rat) / 200000000000000000000), D0 := ((516649284910714285749 : Rat) / 200000000000000000000), D1 := ((153154264910714285749 : Rat) / 200000000000000000000), D2 := ((5062284910714285749 : Rat) / 200000000000000000000), D3 := ((5062284910714285749 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((25073334080821963 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516649284910714285749 : Rat) / 200000000000000000000), R := ((260855784910714285749 : Rat) / 100000000000000000000), D0 := ((260855784910714285749 : Rat) / 100000000000000000000), D1 := ((79108274910714285749 : Rat) / 100000000000000000000), D2 := ((5062284910714285749 : Rat) / 100000000000000000000), D3 := ((15186854732142857247 : Rat) / 200000000000000000000), D4 := ((37824740803571408643 : Rat) / 200000000000000000000), LB := ((16030115187978977 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((260855784910714285749 : Rat) / 100000000000000000000), R := ((526773854732142857247 : Rat) / 200000000000000000000), D0 := ((526773854732142857247 : Rat) / 200000000000000000000), D1 := ((163278834732142857247 : Rat) / 200000000000000000000), D2 := ((15186854732142857247 : Rat) / 200000000000000000000), D3 := ((5062284910714285749 : Rat) / 100000000000000000000), D4 := ((16381227946428561447 : Rat) / 100000000000000000000), LB := ((4222994743410463 : Rat) / 100000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((526773854732142857247 : Rat) / 200000000000000000000), R := ((132959034910714285749 : Rat) / 50000000000000000000), D0 := ((132959034910714285749 : Rat) / 50000000000000000000), D1 := ((42085279910714285749 : Rat) / 50000000000000000000), D2 := ((5062284910714285749 : Rat) / 50000000000000000000), D3 := ((5062284910714285749 : Rat) / 200000000000000000000), D4 := ((5540034196428567429 : Rat) / 40000000000000000000), LB := ((6130808989857167 : Rat) / 50000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((132959034910714285749 : Rat) / 50000000000000000000), R := ((53616359357142857169 : Rat) / 20000000000000000000), D0 := ((53616359357142857169 : Rat) / 20000000000000000000), D1 := ((17266857357142857169 : Rat) / 20000000000000000000), D2 := ((2457659357142857169 : Rat) / 20000000000000000000), D3 := ((2163726964285714347 : Rat) / 100000000000000000000), D4 := ((5659471517857137849 : Rat) / 50000000000000000000), LB := ((3387695814666987 : Rat) / 25000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((53616359357142857169 : Rat) / 20000000000000000000), R := ((4222586308593750003 : Rat) / 1562500000000000000), D0 := ((4222586308593750003 : Rat) / 1562500000000000000), D1 := ((1382781464843750003 : Rat) / 1562500000000000000), D2 := ((225812871093750003 : Rat) / 1562500000000000000), D3 := ((2163726964285714347 : Rat) / 50000000000000000000), D4 := ((9155216071428561351 : Rat) / 100000000000000000000), LB := ((5246965101072809 : Rat) / 250000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4222586308593750003 : Rat) / 1562500000000000000), R := ((542654774464285714731 : Rat) / 200000000000000000000), D0 := ((542654774464285714731 : Rat) / 200000000000000000000), D1 := ((179159754464285714731 : Rat) / 200000000000000000000), D2 := ((31067774464285714731 : Rat) / 200000000000000000000), D3 := ((2163726964285714347 : Rat) / 40000000000000000000), D4 := ((1747872276785711751 : Rat) / 25000000000000000000), LB := ((6188272998710387 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((542654774464285714731 : Rat) / 200000000000000000000), R := ((1087473275892857143809 : Rat) / 400000000000000000000), D0 := ((1087473275892857143809 : Rat) / 400000000000000000000), D1 := ((360483235892857143809 : Rat) / 400000000000000000000), D2 := ((64299275892857143809 : Rat) / 400000000000000000000), D3 := ((23800996607142857817 : Rat) / 400000000000000000000), D4 := ((11819251249999979661 : Rat) / 200000000000000000000), LB := ((121556561669387 : Rat) / 20000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1087473275892857143809 : Rat) / 400000000000000000000), R := ((435422055750000000393 : Rat) / 160000000000000000000), D0 := ((435422055750000000393 : Rat) / 160000000000000000000), D1 := ((144626039750000000393 : Rat) / 160000000000000000000), D2 := ((26152455750000000393 : Rat) / 160000000000000000000), D3 := ((49765720178571429981 : Rat) / 800000000000000000000), D4 := ((858991021428569799 : Rat) / 16000000000000000000), LB := ((8214672432585779 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((435422055750000000393 : Rat) / 160000000000000000000), R := ((272409250714285714539 : Rat) / 100000000000000000000), D0 := ((272409250714285714539 : Rat) / 100000000000000000000), D1 := ((90661740714285714539 : Rat) / 100000000000000000000), D2 := ((16615750714285714539 : Rat) / 100000000000000000000), D3 := ((6491180892857143041 : Rat) / 100000000000000000000), D4 := ((40785824107142775603 : Rat) / 800000000000000000000), LB := ((897554933086897 : Rat) / 200000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272409250714285714539 : Rat) / 100000000000000000000), R := ((2181437732678571430659 : Rat) / 800000000000000000000), D0 := ((2181437732678571430659 : Rat) / 800000000000000000000), D1 := ((727457652678571430659 : Rat) / 800000000000000000000), D2 := ((135089732678571430659 : Rat) / 800000000000000000000), D3 := ((2163726964285714347 : Rat) / 32000000000000000000), D4 := ((4827762142857132657 : Rat) / 100000000000000000000), LB := ((14427840628031263 : Rat) / 10000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2181437732678571430659 : Rat) / 800000000000000000000), R := ((873007838464285715133 : Rat) / 320000000000000000000), D0 := ((873007838464285715133 : Rat) / 320000000000000000000), D1 := ((291415806464285715133 : Rat) / 320000000000000000000), D2 := ((54468638464285715133 : Rat) / 320000000000000000000), D3 := ((110350075178571431697 : Rat) / 1600000000000000000000), D4 := ((36458370178571346909 : Rat) / 800000000000000000000), LB := ((4259896138356201 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((873007838464285715133 : Rat) / 320000000000000000000), R := ((1091800729821428572503 : Rat) / 400000000000000000000), D0 := ((1091800729821428572503 : Rat) / 400000000000000000000), D1 := ((364810689821428572503 : Rat) / 400000000000000000000), D2 := ((68626729821428572503 : Rat) / 400000000000000000000), D3 := ((28128450535714286511 : Rat) / 400000000000000000000), D4 := ((70753013392856979471 : Rat) / 1600000000000000000000), LB := ((8258066402059283 : Rat) / 2500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1091800729821428572503 : Rat) / 400000000000000000000), R := ((4369366646250000004359 : Rat) / 1600000000000000000000), D0 := ((4369366646250000004359 : Rat) / 1600000000000000000000), D1 := ((1461406486250000004359 : Rat) / 1600000000000000000000), D2 := ((276670646250000004359 : Rat) / 1600000000000000000000), D3 := ((114677529107142860391 : Rat) / 1600000000000000000000), D4 := ((17147321607142816281 : Rat) / 400000000000000000000), LB := ((634772583327281 : Rat) / 250000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4369366646250000004359 : Rat) / 1600000000000000000000), R := ((2185765186607142859353 : Rat) / 800000000000000000000), D0 := ((2185765186607142859353 : Rat) / 800000000000000000000), D1 := ((731785106607142859353 : Rat) / 800000000000000000000), D2 := ((139417186607142859353 : Rat) / 800000000000000000000), D3 := ((58420628035714287369 : Rat) / 800000000000000000000), D4 := ((66425559464285550777 : Rat) / 1600000000000000000000), LB := ((986834674224557 : Rat) / 500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2185765186607142859353 : Rat) / 800000000000000000000), R := ((4373694100178571433053 : Rat) / 1600000000000000000000), D0 := ((4373694100178571433053 : Rat) / 1600000000000000000000), D1 := ((1465733940178571433053 : Rat) / 1600000000000000000000), D2 := ((280998100178571433053 : Rat) / 1600000000000000000000), D3 := ((23800996607142857817 : Rat) / 320000000000000000000), D4 := ((6426183249999983643 : Rat) / 160000000000000000000), LB := ((2017618813763139 : Rat) / 1250000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4373694100178571433053 : Rat) / 1600000000000000000000), R := ((21879289135714285737 : Rat) / 8000000000000000000), D0 := ((21879289135714285737 : Rat) / 8000000000000000000), D1 := ((7339488335714285737 : Rat) / 8000000000000000000), D2 := ((1415809135714285737 : Rat) / 8000000000000000000), D3 := ((15146088750000000429 : Rat) / 200000000000000000000), D4 := ((62098105535714122083 : Rat) / 1600000000000000000000), LB := ((734276931756983 : Rat) / 500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21879289135714285737 : Rat) / 8000000000000000000), R := ((4378021554107142861747 : Rat) / 1600000000000000000000), D0 := ((4378021554107142861747 : Rat) / 1600000000000000000000), D1 := ((1470061394107142861747 : Rat) / 1600000000000000000000), D2 := ((285325554107142861747 : Rat) / 1600000000000000000000), D3 := ((123332436964285717779 : Rat) / 1600000000000000000000), D4 := ((7491797321428550967 : Rat) / 200000000000000000000), LB := ((3866033926886031 : Rat) / 2500000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4378021554107142861747 : Rat) / 1600000000000000000000), R := ((2190092640535714288047 : Rat) / 800000000000000000000), D0 := ((2190092640535714288047 : Rat) / 800000000000000000000), D1 := ((736112560535714288047 : Rat) / 800000000000000000000), D2 := ((143744640535714288047 : Rat) / 800000000000000000000), D3 := ((62748081964285716063 : Rat) / 800000000000000000000), D4 := ((57770651607142693389 : Rat) / 1600000000000000000000), LB := ((464593761541357 : Rat) / 250000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2190092640535714288047 : Rat) / 800000000000000000000), R := ((4382349008035714290441 : Rat) / 1600000000000000000000), D0 := ((4382349008035714290441 : Rat) / 1600000000000000000000), D1 := ((1474388848035714290441 : Rat) / 1600000000000000000000), D2 := ((289653008035714290441 : Rat) / 1600000000000000000000), D3 := ((127659890892857146473 : Rat) / 1600000000000000000000), D4 := ((27803462321428489521 : Rat) / 800000000000000000000), LB := ((24166549053001307 : Rat) / 10000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4382349008035714290441 : Rat) / 1600000000000000000000), R := ((1096128183750000001197 : Rat) / 400000000000000000000), D0 := ((1096128183750000001197 : Rat) / 400000000000000000000), D1 := ((369138143750000001197 : Rat) / 400000000000000000000), D2 := ((72954183750000001197 : Rat) / 400000000000000000000), D3 := ((6491180892857143041 : Rat) / 80000000000000000000), D4 := ((10688639535714252939 : Rat) / 320000000000000000000), LB := ((323520625164031 : Rat) / 100000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1096128183750000001197 : Rat) / 400000000000000000000), R := ((877335292392857143827 : Rat) / 320000000000000000000), D0 := ((877335292392857143827 : Rat) / 320000000000000000000), D1 := ((295743260392857143827 : Rat) / 320000000000000000000), D2 := ((58796092392857143827 : Rat) / 320000000000000000000), D3 := ((131987344821428575167 : Rat) / 1600000000000000000000), D4 := ((12819867678571387587 : Rat) / 400000000000000000000), LB := ((4329986779034289 : Rat) / 1000000000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((877335292392857143827 : Rat) / 320000000000000000000), R := ((2194420094464285716741 : Rat) / 800000000000000000000), D0 := ((2194420094464285716741 : Rat) / 800000000000000000000), D1 := ((740440014464285716741 : Rat) / 800000000000000000000), D2 := ((148072094464285716741 : Rat) / 800000000000000000000), D3 := ((67075535892857144757 : Rat) / 800000000000000000000), D4 := ((49115743749999836001 : Rat) / 1600000000000000000000), LB := ((285964315751 : Rat) / 50000000000000) },
  { w1 := ((4364504206452013 : Rat) / 5000000000000000), w2 := ((23617266813961667 : Rat) / 500000000000000000), w3 := ((7703336001297899 : Rat) / 50000000000000000), w4 := ((6970803274157947 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132959034910714285749 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2194420094464285716741 : Rat) / 800000000000000000000), R := ((137286488839285714443 : Rat) / 50000000000000000000), D0 := ((137286488839285714443 : Rat) / 50000000000000000000), D1 := ((46412733839285714443 : Rat) / 50000000000000000000), D2 := ((9389738839285714443 : Rat) / 50000000000000000000), D3 := ((2163726964285714347 : Rat) / 25000000000000000000), D4 := ((23476008392857060827 : Rat) / 800000000000000000000), LB := ((5782408425555663 : Rat) / 2000000000000000000) }
]

def block367RightChunk000L : Rat := ((5454794642857142867 : Rat) / 3125000000000000000)
def block367RightChunk000R : Rat := ((137286488839285714443 : Rat) / 50000000000000000000)

def block367RightChunk000Certificate : Bool :=
  allBoxesValid block367RightChunk000 &&
  coversFromBool block367RightChunk000 block367RightChunk000L block367RightChunk000R

theorem block367RightChunk000Certificate_eq_true :
    block367RightChunk000Certificate = true := by
  native_decide

def block367RightChainCertificate : Bool :=
  decide (
    block367RightL = ((5454794642857142867 : Rat) / 3125000000000000000) /\
    ((137286488839285714443 : Rat) / 50000000000000000000) = block367RightR)

theorem block367RightChainCertificate_eq_true :
    block367RightChainCertificate = true := by
  native_decide

def block367LeftBoxCount : Nat := boxCount block367LeftBoxes
def block367RightBoxCount : Nat := 59

def block367_rational_certificate : Prop :=
    block367LeftCertificate = true /\
    block367RightChainCertificate = true /\
    block367RightChunk000Certificate = true

theorem block367_rational_certificate_proof :
    block367_rational_certificate := by
  exact ⟨block367LeftCertificate_eq_true, block367RightChainCertificate_eq_true, block367RightChunk000Certificate_eq_true⟩

end Block367
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block367

open Set

def block367W1 : Rat := ((4364504206452013 : Rat) / 5000000000000000)
def block367W2 : Rat := ((23617266813961667 : Rat) / 500000000000000000)
def block367W3 : Rat := ((7703336001297899 : Rat) / 50000000000000000)
def block367W4 : Rat := ((6970803274157947 : Rat) / 50000000000000000)
def block367S1 : Rat := ((18174751 : Rat) / 10000000)
def block367S2 : Rat := ((511587 : Rat) / 200000)
def block367S3 : Rat := ((132959034910714285749 : Rat) / 50000000000000000000)
def block367S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block367V (y : ℝ) : ℝ :=
  ratPotential block367W1 block367W2 block367W3 block367W4 block367S1 block367S2 block367S3 block367S4 y

def block367LeftParamsCertificate : Bool :=
  allBoxesSameParams block367LeftBoxes block367W1 block367W2 block367W3 block367W4 block367S1 block367S2 block367S3 block367S4

theorem block367LeftParamsCertificate_eq_true :
    block367LeftParamsCertificate = true := by
  native_decide

theorem block367_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block367LeftL : ℝ) (block367LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block367S1 : ℝ))
    (hy2ne : y ≠ (block367S2 : ℝ))
    (hy3ne : y ≠ (block367S3 : ℝ))
    (hy4ne : y ≠ (block367S4 : ℝ)) :
    0 < block367V y := by
  have hcert := block367LeftCertificate_eq_true
  unfold block367LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block367LeftBoxes) (lo := block367LeftL) (hi := block367LeftR)
    (w1 := block367W1) (w2 := block367W2) (w3 := block367W3) (w4 := block367W4)
    (s1 := block367S1) (s2 := block367S2) (s3 := block367S3) (s4 := block367S4)
    hboxes hcover block367LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block367RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block367RightChunk000 block367W1 block367W2 block367W3 block367W4 block367S1 block367S2 block367S3 block367S4

theorem block367RightChunk000ParamsCertificate_eq_true :
    block367RightChunk000ParamsCertificate = true := by
  native_decide

theorem block367_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block367RightChunk000L : ℝ) (block367RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block367S1 : ℝ))
    (hy2ne : y ≠ (block367S2 : ℝ))
    (hy3ne : y ≠ (block367S3 : ℝ))
    (hy4ne : y ≠ (block367S4 : ℝ)) :
    0 < block367V y := by
  have hcert := block367RightChunk000Certificate_eq_true
  unfold block367RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block367RightChunk000) (lo := block367RightChunk000L) (hi := block367RightChunk000R)
    (w1 := block367W1) (w2 := block367W2) (w3 := block367W3) (w4 := block367W4)
    (s1 := block367S1) (s2 := block367S2) (s3 := block367S3) (s4 := block367S4)
    hboxes hcover block367RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block367_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block367RightL : ℝ) (block367RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block367S1 : ℝ))
    (hy2ne : y ≠ (block367S2 : ℝ))
    (hy3ne : y ≠ (block367S3 : ℝ))
    (hy4ne : y ≠ (block367S4 : ℝ)) :
    0 < block367V y := by
  have hL : (block367RightChunk000L : ℝ) = (block367RightL : ℝ) := by
    norm_num [block367RightChunk000L, block367RightL]
  have hR : (block367RightChunk000R : ℝ) = (block367RightR : ℝ) := by
    norm_num [block367RightChunk000R, block367RightR]
  have hyc : y ∈ Icc (block367RightChunk000L : ℝ) (block367RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block367_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block367_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block367LeftL : ℝ) (block367LeftR : ℝ) →
    y ≠ 0 → y ≠ (block367S1 : ℝ) → y ≠ (block367S2 : ℝ) →
    y ≠ (block367S3 : ℝ) → y ≠ (block367S4 : ℝ) → 0 < block367V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block367RightL : ℝ) (block367RightR : ℝ) →
    y ≠ 0 → y ≠ (block367S1 : ℝ) → y ≠ (block367S2 : ℝ) →
    y ≠ (block367S3 : ℝ) → y ≠ (block367S4 : ℝ) → 0 < block367V y)

theorem block367_reallog_certificate_proof :
    block367_reallog_certificate := by
  exact ⟨block367_left_V_pos, block367_right_V_pos⟩

end Block367
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block367.block367V
#check Erdos1038Lean.M1817475.Block367.block367_left_V_pos
#check Erdos1038Lean.M1817475.Block367.block367_right_V_pos
#check Erdos1038Lean.M1817475.Block367.block367_reallog_certificate_proof
