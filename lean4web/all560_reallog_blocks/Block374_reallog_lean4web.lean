/-
Self-contained Lean4Web paste file.
Block 374 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block374

def block374LeftL : Rat := ((297666339285714287 : Rat) / 400000000000000000)
def block374LeftR : Rat := ((18609033482142857223 : Rat) / 25000000000000000000)
def block374RightL : Rat := ((697666339285714287 : Rat) / 400000000000000000)
def block374RightR : Rat := ((68609033482142857223 : Rat) / 25000000000000000000)

def block374LeftBoxes : List RatBox := [
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((297666339285714287 : Rat) / 400000000000000000), R := ((18609033482142857223 : Rat) / 25000000000000000000), D0 := ((18609033482142857223 : Rat) / 25000000000000000000), D1 := ((429323700714285713 : Rat) / 400000000000000000), D2 := ((725507660714285713 : Rat) / 400000000000000000), D3 := ((2390347468749999997 : Rat) / 1250000000000000000), D4 := ((101410214017857137723 : Rat) / 50000000000000000000), LB := ((6200149914330891 : Rat) / 1000000000000000000) }
]

def block374LeftCertificate : Bool :=
  allBoxesValid block374LeftBoxes &&
  coversFromBool block374LeftBoxes block374LeftL block374LeftR

theorem block374LeftCertificate_eq_true :
    block374LeftCertificate = true := by
  native_decide

def block374RightChunk000 : List RatBox := [
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((697666339285714287 : Rat) / 400000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((29323700714285713 : Rat) / 400000000000000000), D2 := ((325507660714285713 : Rat) / 400000000000000000), D3 := ((1140347468749999997 : Rat) / 1250000000000000000), D4 := ((51410214017857137723 : Rat) / 50000000000000000000), LB := ((8354986620162139 : Rat) / 5000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((8389687232142857151 : Rat) / 10000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((6002810329959427 : Rat) / 50000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((4687387732142857151 : Rat) / 10000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((3935169340610997 : Rat) / 50000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((3761812857142857151 : Rat) / 10000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((2428574349716913 : Rat) / 50000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3299025419642857151 : Rat) / 10000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((21651148283969697 : Rat) / 500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((3067631700892857151 : Rat) / 10000000000000000000), D4 := ((10567236886160711799 : Rat) / 25000000000000000000), LB := ((82564421314051 : Rat) / 4000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((2836237982142857151 : Rat) / 10000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((91489007501111 : Rat) / 62500000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((2604844263392857151 : Rat) / 10000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((150222646182267 : Rat) / 20000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((2489147404017857151 : Rat) / 10000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((1898871994068907 : Rat) / 2000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((2373450544642857151 : Rat) / 10000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((12048513252342019 : Rat) / 2000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((2315602114955357151 : Rat) / 10000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((36460379959886713 : Rat) / 10000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2257753685267857151 : Rat) / 10000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((3937717376279251 : Rat) / 2500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2199905255580357151 : Rat) / 10000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((250115813713353 : Rat) / 50000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((2170981040736607151 : Rat) / 10000000000000000000), D4 := ((8325610235770086799 : Rat) / 25000000000000000000), LB := ((4231986195002507 : Rat) / 1000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2142056825892857151 : Rat) / 10000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((1773843973943423 : Rat) / 500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((2113132611049107151 : Rat) / 10000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((92237546908811 : Rat) / 31250000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2084208396205357151 : Rat) / 10000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((152878464503731 : Rat) / 62500000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((2055284181361607151 : Rat) / 10000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((10167702789909139 : Rat) / 5000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2026359966517857151 : Rat) / 10000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((3433450618313627 : Rat) / 2000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((1997435751674107151 : Rat) / 10000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((3746182822422367 : Rat) / 2500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((1968511536830357151 : Rat) / 10000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((6909311200413437 : Rat) / 5000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((1939587321986607151 : Rat) / 10000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((6851040932345509 : Rat) / 5000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((1910663107142857151 : Rat) / 10000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((1833862059450013 : Rat) / 1250000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((1881738892299107151 : Rat) / 10000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((16763781294669433 : Rat) / 10000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((1852814677455357151 : Rat) / 10000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((1001136137557257 : Rat) / 500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((1823890462611607151 : Rat) / 10000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((3061672136216477 : Rat) / 1250000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((1794966247767857151 : Rat) / 10000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((15112767772045843 : Rat) / 5000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((1766042032924107151 : Rat) / 10000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((465920881051473 : Rat) / 125000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((1737117818080357151 : Rat) / 10000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((1142439512847343 : Rat) / 250000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((1708193603236607151 : Rat) / 10000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((11112631478540691 : Rat) / 2000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((1679269388392857151 : Rat) / 10000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((18491491676470573 : Rat) / 10000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((1621420958705357151 : Rat) / 10000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((4646885253194649 : Rat) / 1000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((1563572529017857151 : Rat) / 10000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((81604705532283 : Rat) / 10000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((1505724099330357151 : Rat) / 10000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((6244298935200329 : Rat) / 500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1447875669642857151 : Rat) / 10000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((8384058053454713 : Rat) / 1000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1332178810267857151 : Rat) / 10000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((11334567118038999 : Rat) / 500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1216481950892857151 : Rat) / 10000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((5224798806012021 : Rat) / 200000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((103302488232142857151 : Rat) / 40000000000000000000), D0 := ((103302488232142857151 : Rat) / 40000000000000000000), D1 := ((30603484232142857151 : Rat) / 40000000000000000000), D2 := ((985088232142857151 : Rat) / 40000000000000000000), D3 := ((985088232142857151 : Rat) / 10000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((3275540249493597 : Rat) / 100000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((103302488232142857151 : Rat) / 40000000000000000000), R := ((52143788232142857151 : Rat) / 20000000000000000000), D0 := ((52143788232142857151 : Rat) / 20000000000000000000), D1 := ((15794286232142857151 : Rat) / 20000000000000000000), D2 := ((985088232142857151 : Rat) / 20000000000000000000), D3 := ((2955264696428571453 : Rat) / 40000000000000000000), D4 := ((37961584553571408637 : Rat) / 200000000000000000000), LB := ((2548840303844979 : Rat) / 100000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((52143788232142857151 : Rat) / 20000000000000000000), R := ((26564438232142857151 : Rat) / 10000000000000000000), D0 := ((26564438232142857151 : Rat) / 10000000000000000000), D1 := ((8389687232142857151 : Rat) / 10000000000000000000), D2 := ((985088232142857151 : Rat) / 10000000000000000000), D3 := ((985088232142857151 : Rat) / 20000000000000000000), D4 := ((16518071696428561441 : Rat) / 100000000000000000000), LB := ((155115686023867 : Rat) / 31250000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((26564438232142857151 : Rat) / 10000000000000000000), R := ((535684640446428571711 : Rat) / 200000000000000000000), D0 := ((535684640446428571711 : Rat) / 200000000000000000000), D1 := ((172189620446428571711 : Rat) / 200000000000000000000), D2 := ((24097640446428571711 : Rat) / 200000000000000000000), D3 := ((4395875803571428691 : Rat) / 200000000000000000000), D4 := ((5796315267857137843 : Rat) / 50000000000000000000), LB := ((7028790949109029 : Rat) / 50000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((535684640446428571711 : Rat) / 200000000000000000000), R := ((270040258125000000201 : Rat) / 100000000000000000000), D0 := ((270040258125000000201 : Rat) / 100000000000000000000), D1 := ((88292748125000000201 : Rat) / 100000000000000000000), D2 := ((14246758125000000201 : Rat) / 100000000000000000000), D3 := ((4395875803571428691 : Rat) / 100000000000000000000), D4 := ((18789385267857122681 : Rat) / 200000000000000000000), LB := ((481637195162109 : Rat) / 20000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((270040258125000000201 : Rat) / 100000000000000000000), R := ((216911381660714285899 : Rat) / 80000000000000000000), D0 := ((216911381660714285899 : Rat) / 80000000000000000000), D1 := ((71513373660714285899 : Rat) / 80000000000000000000), D2 := ((12276581660714285899 : Rat) / 80000000000000000000), D3 := ((4395875803571428691 : Rat) / 80000000000000000000), D4 := ((1439350946428569399 : Rat) / 20000000000000000000), LB := ((4188046555072017 : Rat) / 500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((216911381660714285899 : Rat) / 80000000000000000000), R := ((2173509692410714287681 : Rat) / 800000000000000000000), D0 := ((2173509692410714287681 : Rat) / 800000000000000000000), D1 := ((719529612410714287681 : Rat) / 800000000000000000000), D2 := ((127161692410714287681 : Rat) / 800000000000000000000), D3 := ((48354633839285715601 : Rat) / 800000000000000000000), D4 := ((24391143124999959289 : Rat) / 400000000000000000000), LB := ((484569917556691 : Rat) / 62500000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2173509692410714287681 : Rat) / 800000000000000000000), R := ((4351415260625000004053 : Rat) / 1600000000000000000000), D0 := ((4351415260625000004053 : Rat) / 1600000000000000000000), D1 := ((1443455100625000004053 : Rat) / 1600000000000000000000), D2 := ((258719260625000004053 : Rat) / 1600000000000000000000), D3 := ((101105143482142859893 : Rat) / 1600000000000000000000), D4 := ((44386410446428489887 : Rat) / 800000000000000000000), LB := ((1919674253576531 : Rat) / 200000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4351415260625000004053 : Rat) / 1600000000000000000000), R := ((544476392053571429093 : Rat) / 200000000000000000000), D0 := ((544476392053571429093 : Rat) / 200000000000000000000), D1 := ((180981372053571429093 : Rat) / 200000000000000000000), D2 := ((32889392053571429093 : Rat) / 200000000000000000000), D3 := ((13187627410714286073 : Rat) / 200000000000000000000), D4 := ((84376945089285551083 : Rat) / 1600000000000000000000), LB := ((1129915949376803 : Rat) / 200000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((544476392053571429093 : Rat) / 200000000000000000000), R := ((872041402446428572287 : Rat) / 320000000000000000000), D0 := ((872041402446428572287 : Rat) / 320000000000000000000), D1 := ((290449370446428572287 : Rat) / 320000000000000000000), D2 := ((53502202446428572287 : Rat) / 320000000000000000000), D3 := ((4395875803571428691 : Rat) / 64000000000000000000), D4 := ((9997633660714265299 : Rat) / 200000000000000000000), LB := ((593671459316103 : Rat) / 250000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((872041402446428572287 : Rat) / 320000000000000000000), R := ((8724809900267857151561 : Rat) / 3200000000000000000000), D0 := ((8724809900267857151561 : Rat) / 3200000000000000000000), D1 := ((2908889580267857151561 : Rat) / 3200000000000000000000), D2 := ((539417900267857151561 : Rat) / 3200000000000000000000), D3 := ((224189665982142863241 : Rat) / 3200000000000000000000), D4 := ((75585193482142693701 : Rat) / 1600000000000000000000), LB := ((2505035414374829 : Rat) / 500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8724809900267857151561 : Rat) / 3200000000000000000000), R := ((2182301444017857145063 : Rat) / 800000000000000000000), D0 := ((2182301444017857145063 : Rat) / 800000000000000000000), D1 := ((728321364017857145063 : Rat) / 800000000000000000000), D2 := ((135953444017857145063 : Rat) / 800000000000000000000), D3 := ((57146385446428572983 : Rat) / 800000000000000000000), D4 := ((146774511160713958711 : Rat) / 3200000000000000000000), LB := ((78545701422289 : Rat) / 20000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2182301444017857145063 : Rat) / 800000000000000000000), R := ((8733601651875000008943 : Rat) / 3200000000000000000000), D0 := ((8733601651875000008943 : Rat) / 3200000000000000000000), D1 := ((2917681331875000008943 : Rat) / 3200000000000000000000), D2 := ((548209651875000008943 : Rat) / 3200000000000000000000), D3 := ((232981417589285720623 : Rat) / 3200000000000000000000), D4 := ((7118931767857126501 : Rat) / 160000000000000000000), LB := ((379148041685283 : Rat) / 125000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8733601651875000008943 : Rat) / 3200000000000000000000), R := ((4368998763839285718817 : Rat) / 1600000000000000000000), D0 := ((4368998763839285718817 : Rat) / 1600000000000000000000), D1 := ((1461038603839285718817 : Rat) / 1600000000000000000000), D2 := ((276302763839285718817 : Rat) / 1600000000000000000000), D3 := ((118688646696428574657 : Rat) / 1600000000000000000000), D4 := ((137982759553571101329 : Rat) / 3200000000000000000000), LB := ((1166718858468807 : Rat) / 500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4368998763839285718817 : Rat) / 1600000000000000000000), R := ((349695736139285714653 : Rat) / 128000000000000000000), D0 := ((349695736139285714653 : Rat) / 128000000000000000000), D1 := ((117058923339285714653 : Rat) / 128000000000000000000), D2 := ((22280056139285714653 : Rat) / 128000000000000000000), D3 := ((48354633839285715601 : Rat) / 640000000000000000000), D4 := ((66793441874999836319 : Rat) / 1600000000000000000000), LB := ((18346002381878779 : Rat) / 10000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((349695736139285714653 : Rat) / 128000000000000000000), R := ((1093348659910714286877 : Rat) / 400000000000000000000), D0 := ((1093348659910714286877 : Rat) / 400000000000000000000), D1 := ((366358619910714286877 : Rat) / 400000000000000000000), D2 := ((70174659910714286877 : Rat) / 400000000000000000000), D3 := ((30771130625000000837 : Rat) / 400000000000000000000), D4 := ((129191007946428243947 : Rat) / 3200000000000000000000), LB := ((3088413531715517 : Rat) / 2000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1093348659910714286877 : Rat) / 400000000000000000000), R := ((8751185155089285723707 : Rat) / 3200000000000000000000), D0 := ((8751185155089285723707 : Rat) / 3200000000000000000000), D1 := ((2935264835089285723707 : Rat) / 3200000000000000000000), D2 := ((565793155089285723707 : Rat) / 3200000000000000000000), D3 := ((250564920803571435387 : Rat) / 3200000000000000000000), D4 := ((15599391517857101907 : Rat) / 400000000000000000000), LB := ((2941768946959189 : Rat) / 2000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8751185155089285723707 : Rat) / 3200000000000000000000), R := ((4377790515446428576199 : Rat) / 1600000000000000000000), D0 := ((4377790515446428576199 : Rat) / 1600000000000000000000), D1 := ((1469830355446428576199 : Rat) / 1600000000000000000000), D2 := ((285094515446428576199 : Rat) / 1600000000000000000000), D3 := ((127480398303571432039 : Rat) / 1600000000000000000000), D4 := ((24079851267857077313 : Rat) / 640000000000000000000), LB := ((4061218881799139 : Rat) / 2500000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4377790515446428576199 : Rat) / 1600000000000000000000), R := ((8759976906696428581089 : Rat) / 3200000000000000000000), D0 := ((8759976906696428581089 : Rat) / 3200000000000000000000), D1 := ((2944056586696428581089 : Rat) / 3200000000000000000000), D2 := ((574584906696428581089 : Rat) / 3200000000000000000000), D3 := ((259356672410714292769 : Rat) / 3200000000000000000000), D4 := ((58001690267856978937 : Rat) / 1600000000000000000000), LB := ((2016258935871651 : Rat) / 1000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8759976906696428581089 : Rat) / 3200000000000000000000), R := ((438218639125000000489 : Rat) / 160000000000000000000), D0 := ((438218639125000000489 : Rat) / 160000000000000000000), D1 := ((147422623125000000489 : Rat) / 160000000000000000000), D2 := ((28949039125000000489 : Rat) / 160000000000000000000), D3 := ((13187627410714286073 : Rat) / 160000000000000000000), D4 := ((111607504732142529183 : Rat) / 3200000000000000000000), LB := ((53180501776533 : Rat) / 20000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((438218639125000000489 : Rat) / 160000000000000000000), R := ((8768768658303571438471 : Rat) / 3200000000000000000000), D0 := ((8768768658303571438471 : Rat) / 3200000000000000000000), D1 := ((2952848338303571438471 : Rat) / 3200000000000000000000), D2 := ((583376658303571438471 : Rat) / 3200000000000000000000), D3 := ((268148424017857150151 : Rat) / 3200000000000000000000), D4 := ((26802907232142775123 : Rat) / 800000000000000000000), LB := ((3567431666387233 : Rat) / 1000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8768768658303571438471 : Rat) / 3200000000000000000000), R := ((4386582267053571433581 : Rat) / 1600000000000000000000), D0 := ((4386582267053571433581 : Rat) / 1600000000000000000000), D1 := ((1478622107053571433581 : Rat) / 1600000000000000000000), D2 := ((293886267053571433581 : Rat) / 1600000000000000000000), D3 := ((136272149910714289421 : Rat) / 1600000000000000000000), D4 := ((102815753124999671801 : Rat) / 3200000000000000000000), LB := ((4758230129112417 : Rat) / 1000000000000000000) },
  { w1 := ((4302110285965343 : Rat) / 5000000000000000), w2 := ((4690307221895797 : Rat) / 100000000000000000), w3 := ((7805681711712567 : Rat) / 50000000000000000), w4 := ((2800603080335723 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26564438232142857151 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4386582267053571433581 : Rat) / 1600000000000000000000), R := ((68609033482142857223 : Rat) / 25000000000000000000), D0 := ((68609033482142857223 : Rat) / 25000000000000000000), D1 := ((23172155982142857223 : Rat) / 25000000000000000000), D2 := ((4660658482142857223 : Rat) / 25000000000000000000), D3 := ((4395875803571428691 : Rat) / 50000000000000000000), D4 := ((9841987732142824311 : Rat) / 320000000000000000000), LB := ((2085459580903129 : Rat) / 1250000000000000000) }
]

def block374RightChunk000L : Rat := ((697666339285714287 : Rat) / 400000000000000000)
def block374RightChunk000R : Rat := ((68609033482142857223 : Rat) / 25000000000000000000)

def block374RightChunk000Certificate : Bool :=
  allBoxesValid block374RightChunk000 &&
  coversFromBool block374RightChunk000 block374RightChunk000L block374RightChunk000R

theorem block374RightChunk000Certificate_eq_true :
    block374RightChunk000Certificate = true := by
  native_decide

def block374RightChainCertificate : Bool :=
  decide (
    block374RightL = ((697666339285714287 : Rat) / 400000000000000000) /\
    ((68609033482142857223 : Rat) / 25000000000000000000) = block374RightR)

theorem block374RightChainCertificate_eq_true :
    block374RightChainCertificate = true := by
  native_decide

def block374LeftBoxCount : Nat := boxCount block374LeftBoxes
def block374RightBoxCount : Nat := 60

def block374_rational_certificate : Prop :=
    block374LeftCertificate = true /\
    block374RightChainCertificate = true /\
    block374RightChunk000Certificate = true

theorem block374_rational_certificate_proof :
    block374_rational_certificate := by
  exact ⟨block374LeftCertificate_eq_true, block374RightChainCertificate_eq_true, block374RightChunk000Certificate_eq_true⟩

end Block374
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block374

open Set

def block374W1 : Rat := ((4302110285965343 : Rat) / 5000000000000000)
def block374W2 : Rat := ((4690307221895797 : Rat) / 100000000000000000)
def block374W3 : Rat := ((7805681711712567 : Rat) / 50000000000000000)
def block374W4 : Rat := ((2800603080335723 : Rat) / 20000000000000000)
def block374S1 : Rat := ((18174751 : Rat) / 10000000)
def block374S2 : Rat := ((511587 : Rat) / 200000)
def block374S3 : Rat := ((26564438232142857151 : Rat) / 10000000000000000000)
def block374S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block374V (y : ℝ) : ℝ :=
  ratPotential block374W1 block374W2 block374W3 block374W4 block374S1 block374S2 block374S3 block374S4 y

def block374LeftParamsCertificate : Bool :=
  allBoxesSameParams block374LeftBoxes block374W1 block374W2 block374W3 block374W4 block374S1 block374S2 block374S3 block374S4

theorem block374LeftParamsCertificate_eq_true :
    block374LeftParamsCertificate = true := by
  native_decide

theorem block374_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block374LeftL : ℝ) (block374LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block374S1 : ℝ))
    (hy2ne : y ≠ (block374S2 : ℝ))
    (hy3ne : y ≠ (block374S3 : ℝ))
    (hy4ne : y ≠ (block374S4 : ℝ)) :
    0 < block374V y := by
  have hcert := block374LeftCertificate_eq_true
  unfold block374LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block374LeftBoxes) (lo := block374LeftL) (hi := block374LeftR)
    (w1 := block374W1) (w2 := block374W2) (w3 := block374W3) (w4 := block374W4)
    (s1 := block374S1) (s2 := block374S2) (s3 := block374S3) (s4 := block374S4)
    hboxes hcover block374LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block374RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block374RightChunk000 block374W1 block374W2 block374W3 block374W4 block374S1 block374S2 block374S3 block374S4

theorem block374RightChunk000ParamsCertificate_eq_true :
    block374RightChunk000ParamsCertificate = true := by
  native_decide

theorem block374_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block374RightChunk000L : ℝ) (block374RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block374S1 : ℝ))
    (hy2ne : y ≠ (block374S2 : ℝ))
    (hy3ne : y ≠ (block374S3 : ℝ))
    (hy4ne : y ≠ (block374S4 : ℝ)) :
    0 < block374V y := by
  have hcert := block374RightChunk000Certificate_eq_true
  unfold block374RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block374RightChunk000) (lo := block374RightChunk000L) (hi := block374RightChunk000R)
    (w1 := block374W1) (w2 := block374W2) (w3 := block374W3) (w4 := block374W4)
    (s1 := block374S1) (s2 := block374S2) (s3 := block374S3) (s4 := block374S4)
    hboxes hcover block374RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block374_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block374RightL : ℝ) (block374RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block374S1 : ℝ))
    (hy2ne : y ≠ (block374S2 : ℝ))
    (hy3ne : y ≠ (block374S3 : ℝ))
    (hy4ne : y ≠ (block374S4 : ℝ)) :
    0 < block374V y := by
  have hL : (block374RightChunk000L : ℝ) = (block374RightL : ℝ) := by
    norm_num [block374RightChunk000L, block374RightL]
  have hR : (block374RightChunk000R : ℝ) = (block374RightR : ℝ) := by
    norm_num [block374RightChunk000R, block374RightR]
  have hyc : y ∈ Icc (block374RightChunk000L : ℝ) (block374RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block374_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block374_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block374LeftL : ℝ) (block374LeftR : ℝ) →
    y ≠ 0 → y ≠ (block374S1 : ℝ) → y ≠ (block374S2 : ℝ) →
    y ≠ (block374S3 : ℝ) → y ≠ (block374S4 : ℝ) → 0 < block374V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block374RightL : ℝ) (block374RightR : ℝ) →
    y ≠ 0 → y ≠ (block374S1 : ℝ) → y ≠ (block374S2 : ℝ) →
    y ≠ (block374S3 : ℝ) → y ≠ (block374S4 : ℝ) → 0 < block374V y)

theorem block374_reallog_certificate_proof :
    block374_reallog_certificate := by
  exact ⟨block374_left_V_pos, block374_right_V_pos⟩

end Block374
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block374.block374V
#check Erdos1038Lean.M1817475.Block374.block374_left_V_pos
#check Erdos1038Lean.M1817475.Block374.block374_right_V_pos
#check Erdos1038Lean.M1817475.Block374.block374_reallog_certificate_proof
