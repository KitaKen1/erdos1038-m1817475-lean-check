/-
Self-contained Lean4Web paste file.
Block 384 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block384

def block384LeftL : Rat := ((7422109375000000033 : Rat) / 10000000000000000000)
def block384LeftR : Rat := ((290002511160714287 : Rat) / 390625000000000000)
def block384RightL : Rat := ((17422109375000000033 : Rat) / 10000000000000000000)
def block384RightR : Rat := ((1071252511160714287 : Rat) / 390625000000000000)

def block384LeftBoxes : List RatBox := [
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((7422109375000000033 : Rat) / 10000000000000000000), R := ((290002511160714287 : Rat) / 390625000000000000), D0 := ((290002511160714287 : Rat) / 390625000000000000), D1 := ((10752641624999999967 : Rat) / 10000000000000000000), D2 := ((18157240624999999967 : Rat) / 10000000000000000000), D3 := ((9551615321428571417 : Rat) / 5000000000000000000), D4 := ((101507959553571423433 : Rat) / 50000000000000000000), LB := ((3139765839272557 : Rat) / 500000000000000000) }
]

def block384LeftCertificate : Bool :=
  allBoxesValid block384LeftBoxes &&
  coversFromBool block384LeftBoxes block384LeftL block384LeftR

theorem block384LeftCertificate_eq_true :
    block384LeftCertificate = true := by
  native_decide

def block384RightChunk000 : List RatBox := [
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((17422109375000000033 : Rat) / 10000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((752641624999999967 : Rat) / 10000000000000000000), D2 := ((8157240624999999967 : Rat) / 10000000000000000000), D3 := ((4551615321428571417 : Rat) / 5000000000000000000), D4 := ((51507959553571423433 : Rat) / 50000000000000000000), LB := ((16031847883499 : Rat) / 10000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((8350589017857142867 : Rat) / 10000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((10381938965244257 : Rat) / 100000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((4648289517857142867 : Rat) / 10000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((1719061879137337 : Rat) / 25000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((3722714642857142867 : Rat) / 10000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((4128319409455147 : Rat) / 100000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3259927205357142867 : Rat) / 10000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((374076704229387 : Rat) / 10000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((3028533486607142867 : Rat) / 10000000000000000000), D4 := ((10567236886160711799 : Rat) / 25000000000000000000), LB := ((198033988317539 : Rat) / 12500000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((2797139767857142867 : Rat) / 10000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((3927489312065341 : Rat) / 200000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((2681442908482142867 : Rat) / 10000000000000000000), D4 := ((9699510440848211799 : Rat) / 25000000000000000000), LB := ((58105146683749 : Rat) / 5000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((2565746049107142867 : Rat) / 10000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((459340625840729 : Rat) / 100000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((2450049189732142867 : Rat) / 10000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((2286359964127009 : Rat) / 250000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((123561673 : Rat) / 51200000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((2392200760044642867 : Rat) / 10000000000000000000), D4 := ((8976405069754461799 : Rat) / 25000000000000000000), LB := ((161972807837827 : Rat) / 25000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((2334352330357142867 : Rat) / 10000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((4099874584145263 : Rat) / 1000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((2276503900669642867 : Rat) / 10000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((20190145402819437 : Rat) / 10000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2218655470982142867 : Rat) / 10000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((1241627299850001 : Rat) / 5000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2160807041294642867 : Rat) / 10000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((19488985852751939 : Rat) / 5000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((2131882826450892867 : Rat) / 10000000000000000000), D4 := ((8325610235770086799 : Rat) / 25000000000000000000), LB := ((16404393326878153 : Rat) / 5000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2102958611607142867 : Rat) / 10000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((5501826374243679 : Rat) / 2000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((2074034396763392867 : Rat) / 10000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((462024969415431 : Rat) / 200000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2045110181919642867 : Rat) / 10000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((9804439579666757 : Rat) / 5000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((2016185967075892867 : Rat) / 10000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((2132175629943403 : Rat) / 1250000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((1987261752232142867 : Rat) / 10000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((1547399979687003 : Rat) / 1000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((1958337537388392867 : Rat) / 10000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((930487755388381 : Rat) / 625000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((1929413322544642867 : Rat) / 10000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((3832530872706491 : Rat) / 2500000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((1900489107700892867 : Rat) / 10000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((16834654116519299 : Rat) / 10000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((1871564892857142867 : Rat) / 10000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((19437740742798137 : Rat) / 10000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((1842640678013392867 : Rat) / 10000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((181083386930857 : Rat) / 78125000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((1813716463169642867 : Rat) / 10000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((5620006122530219 : Rat) / 2000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((1784792248325892867 : Rat) / 10000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((136992302831761 : Rat) / 40000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((1755868033482142867 : Rat) / 10000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((8334644381177203 : Rat) / 2000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((1726943818638392867 : Rat) / 10000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((2521528792063743 : Rat) / 500000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((1698019603794642867 : Rat) / 10000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((12539544589683371 : Rat) / 10000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((1640171174107142867 : Rat) / 10000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((3762954234632493 : Rat) / 1000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((1582322744419642867 : Rat) / 10000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((13836240689435897 : Rat) / 2000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((1524474314732142867 : Rat) / 10000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((2875110447546847 : Rat) / 2000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1408777455357142867 : Rat) / 10000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((11921247217053621 : Rat) / 1000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1293080595982142867 : Rat) / 10000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((13497019187640999 : Rat) / 500000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1177383736607142867 : Rat) / 10000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((7883129464714901 : Rat) / 250000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((103263390017857142867 : Rat) / 40000000000000000000), D0 := ((103263390017857142867 : Rat) / 40000000000000000000), D1 := ((30564386017857142867 : Rat) / 40000000000000000000), D2 := ((945990017857142867 : Rat) / 40000000000000000000), D3 := ((945990017857142867 : Rat) / 10000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((551429916189829 : Rat) / 12500000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((103263390017857142867 : Rat) / 40000000000000000000), R := ((52104690017857142867 : Rat) / 20000000000000000000), D0 := ((52104690017857142867 : Rat) / 20000000000000000000), D1 := ((15755188017857142867 : Rat) / 20000000000000000000), D2 := ((945990017857142867 : Rat) / 20000000000000000000), D3 := ((2837970053571428601 : Rat) / 40000000000000000000), D4 := ((38157075624999980057 : Rat) / 200000000000000000000), LB := ((3953170636074291 : Rat) / 100000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((52104690017857142867 : Rat) / 20000000000000000000), R := ((26525340017857142867 : Rat) / 10000000000000000000), D0 := ((26525340017857142867 : Rat) / 10000000000000000000), D1 := ((8350589017857142867 : Rat) / 10000000000000000000), D2 := ((945990017857142867 : Rat) / 10000000000000000000), D3 := ((945990017857142867 : Rat) / 20000000000000000000), D4 := ((16713562767857132861 : Rat) / 100000000000000000000), LB := ((5892292317955447 : Rat) / 250000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((26525340017857142867 : Rat) / 10000000000000000000), R := ((535000421696428571741 : Rat) / 200000000000000000000), D0 := ((535000421696428571741 : Rat) / 200000000000000000000), D1 := ((171505401696428571741 : Rat) / 200000000000000000000), D2 := ((23413421696428571741 : Rat) / 200000000000000000000), D3 := ((4493621339285714401 : Rat) / 200000000000000000000), D4 := ((5991806339285709263 : Rat) / 50000000000000000000), LB := ((14835431449706743 : Rat) / 100000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((535000421696428571741 : Rat) / 200000000000000000000), R := ((269747021517857143071 : Rat) / 100000000000000000000), D0 := ((269747021517857143071 : Rat) / 100000000000000000000), D1 := ((87999511517857143071 : Rat) / 100000000000000000000), D2 := ((13953521517857143071 : Rat) / 100000000000000000000), D3 := ((4493621339285714401 : Rat) / 100000000000000000000), D4 := ((19473604017857122651 : Rat) / 200000000000000000000), LB := ((5764646950884289 : Rat) / 200000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((269747021517857143071 : Rat) / 100000000000000000000), R := ((216696341482142857337 : Rat) / 80000000000000000000), D0 := ((216696341482142857337 : Rat) / 80000000000000000000), D1 := ((71298333482142857337 : Rat) / 80000000000000000000), D2 := ((12061541482142857337 : Rat) / 80000000000000000000), D3 := ((4493621339285714401 : Rat) / 80000000000000000000), D4 := ((59919930714285633 : Rat) / 800000000000000000), LB := ((5876888575119421 : Rat) / 500000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((216696341482142857337 : Rat) / 80000000000000000000), R := ((2171457036160714287771 : Rat) / 800000000000000000000), D0 := ((2171457036160714287771 : Rat) / 800000000000000000000), D1 := ((717476956160714287771 : Rat) / 800000000000000000000), D2 := ((125109036160714287771 : Rat) / 800000000000000000000), D3 := ((49429834732142858411 : Rat) / 800000000000000000000), D4 := ((25466344017857102099 : Rat) / 400000000000000000000), LB := ((10376210505743999 : Rat) / 1000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2171457036160714287771 : Rat) / 800000000000000000000), R := ((543987664375000000543 : Rat) / 200000000000000000000), D0 := ((543987664375000000543 : Rat) / 200000000000000000000), D1 := ((180492644375000000543 : Rat) / 200000000000000000000), D2 := ((32400664375000000543 : Rat) / 200000000000000000000), D3 := ((13480864017857143203 : Rat) / 200000000000000000000), D4 := ((46439066696428489797 : Rat) / 800000000000000000000), LB := ((5464468016311841 : Rat) / 10000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((543987664375000000543 : Rat) / 200000000000000000000), R := ((871278987267857143749 : Rat) / 320000000000000000000), D0 := ((871278987267857143749 : Rat) / 320000000000000000000), D1 := ((289686955267857143749 : Rat) / 320000000000000000000), D2 := ((52739787267857143749 : Rat) / 320000000000000000000), D3 := ((4493621339285714401 : Rat) / 64000000000000000000), D4 := ((10486361339285693849 : Rat) / 200000000000000000000), LB := ((7836186541207213 : Rat) / 2000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((871278987267857143749 : Rat) / 320000000000000000000), R := ((2180444278839285716573 : Rat) / 800000000000000000000), D0 := ((2180444278839285716573 : Rat) / 800000000000000000000), D1 := ((726464198839285716573 : Rat) / 800000000000000000000), D2 := ((134096278839285716573 : Rat) / 800000000000000000000), D3 := ((58417077410714287213 : Rat) / 800000000000000000000), D4 := ((79397269374999836391 : Rat) / 1600000000000000000000), LB := ((1240313932753187 : Rat) / 1250000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2180444278839285716573 : Rat) / 800000000000000000000), R := ((8726270736696428580693 : Rat) / 3200000000000000000000), D0 := ((8726270736696428580693 : Rat) / 3200000000000000000000), D1 := ((2910350416696428580693 : Rat) / 3200000000000000000000), D2 := ((540878736696428580693 : Rat) / 3200000000000000000000), D3 := ((238161930982142863253 : Rat) / 3200000000000000000000), D4 := ((7490364803571412199 : Rat) / 160000000000000000000), LB := ((19764941646379097 : Rat) / 5000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8726270736696428580693 : Rat) / 3200000000000000000000), R := ((4365382179017857147547 : Rat) / 1600000000000000000000), D0 := ((4365382179017857147547 : Rat) / 1600000000000000000000), D1 := ((1457422019017857147547 : Rat) / 1600000000000000000000), D2 := ((272686179017857147547 : Rat) / 1600000000000000000000), D3 := ((121327776160714288827 : Rat) / 1600000000000000000000), D4 := ((145313674732142529579 : Rat) / 3200000000000000000000), LB := ((15311862455956171 : Rat) / 5000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4365382179017857147547 : Rat) / 1600000000000000000000), R := ((1747051595875000001899 : Rat) / 640000000000000000000), D0 := ((1747051595875000001899 : Rat) / 640000000000000000000), D1 := ((583867531875000001899 : Rat) / 640000000000000000000), D2 := ((109973195875000001899 : Rat) / 640000000000000000000), D3 := ((49429834732142858411 : Rat) / 640000000000000000000), D4 := ((70410026696428407589 : Rat) / 1600000000000000000000), LB := ((23664817559749807 : Rat) / 10000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1747051595875000001899 : Rat) / 640000000000000000000), R := ((1092468950089285715487 : Rat) / 400000000000000000000), D0 := ((1092468950089285715487 : Rat) / 400000000000000000000), D1 := ((365478910089285715487 : Rat) / 400000000000000000000), D2 := ((69294950089285715487 : Rat) / 400000000000000000000), D3 := ((31455349375000000807 : Rat) / 400000000000000000000), D4 := ((136326432053571100777 : Rat) / 3200000000000000000000), LB := ((18720238175681247 : Rat) / 10000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1092468950089285715487 : Rat) / 400000000000000000000), R := ((8744245222053571438297 : Rat) / 3200000000000000000000), D0 := ((8744245222053571438297 : Rat) / 3200000000000000000000), D1 := ((2928324902053571438297 : Rat) / 3200000000000000000000), D2 := ((558853222053571438297 : Rat) / 3200000000000000000000), D3 := ((256136416339285720857 : Rat) / 3200000000000000000000), D4 := ((16479101339285673297 : Rat) / 400000000000000000000), LB := ((15866908372997313 : Rat) / 10000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8744245222053571438297 : Rat) / 3200000000000000000000), R := ((4374369421696428576349 : Rat) / 1600000000000000000000), D0 := ((4374369421696428576349 : Rat) / 1600000000000000000000), D1 := ((1466409261696428576349 : Rat) / 1600000000000000000000), D2 := ((281673421696428576349 : Rat) / 1600000000000000000000), D3 := ((130315018839285717629 : Rat) / 1600000000000000000000), D4 := ((5093567574999986879 : Rat) / 128000000000000000000), LB := ((1899092561488333 : Rat) / 1250000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4374369421696428576349 : Rat) / 1600000000000000000000), R := ((8753232464732142867099 : Rat) / 3200000000000000000000), D0 := ((8753232464732142867099 : Rat) / 3200000000000000000000), D1 := ((2937312144732142867099 : Rat) / 3200000000000000000000), D2 := ((567840464732142867099 : Rat) / 3200000000000000000000), D3 := ((265123659017857149659 : Rat) / 3200000000000000000000), D4 := ((61422784017856978787 : Rat) / 1600000000000000000000), LB := ((2099751126158067 : Rat) / 1250000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8753232464732142867099 : Rat) / 3200000000000000000000), R := ((17515452172142857163 : Rat) / 6400000000000000000), D0 := ((17515452172142857163 : Rat) / 6400000000000000000), D1 := ((5883611532142857163 : Rat) / 6400000000000000000), D2 := ((1144668172142857163 : Rat) / 6400000000000000000), D3 := ((13480864017857143203 : Rat) / 160000000000000000000), D4 := ((118351946696428243173 : Rat) / 3200000000000000000000), LB := ((2079699569991711 : Rat) / 1000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((17515452172142857163 : Rat) / 6400000000000000000), R := ((8762219707410714295901 : Rat) / 3200000000000000000000), D0 := ((8762219707410714295901 : Rat) / 3200000000000000000000), D1 := ((2946299387410714295901 : Rat) / 3200000000000000000000), D2 := ((576827707410714295901 : Rat) / 3200000000000000000000), D3 := ((274110901696428578461 : Rat) / 3200000000000000000000), D4 := ((28464581339285632193 : Rat) / 800000000000000000000), LB := ((5463994061981059 : Rat) / 2000000000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8762219707410714295901 : Rat) / 3200000000000000000000), R := ((4383356664375000005151 : Rat) / 1600000000000000000000), D0 := ((4383356664375000005151 : Rat) / 1600000000000000000000), D1 := ((1475396504375000005151 : Rat) / 1600000000000000000000), D2 := ((290660664375000005151 : Rat) / 1600000000000000000000), D3 := ((139302261517857146431 : Rat) / 1600000000000000000000), D4 := ((109364704017856814371 : Rat) / 3200000000000000000000), LB := ((114111206697581 : Rat) / 31250000000000000) },
  { w1 := ((8429180103914411 : Rat) / 10000000000000000), w2 := ((925197128691713 : Rat) / 20000000000000000), w3 := ((318738628916679 : Rat) / 2000000000000000), w4 := ((3518598311612653 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26525340017857142867 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4383356664375000005151 : Rat) / 1600000000000000000000), R := ((1071252511160714287 : Rat) / 390625000000000000), D0 := ((1071252511160714287 : Rat) / 390625000000000000), D1 := ((361301300223214287 : Rat) / 390625000000000000), D2 := ((72059151785714287 : Rat) / 390625000000000000), D3 := ((4493621339285714401 : Rat) / 50000000000000000000), D4 := ((10487108267857109997 : Rat) / 320000000000000000000), LB := ((9959207717402663 : Rat) / 50000000000000000000) }
]

def block384RightChunk000L : Rat := ((17422109375000000033 : Rat) / 10000000000000000000)
def block384RightChunk000R : Rat := ((1071252511160714287 : Rat) / 390625000000000000)

def block384RightChunk000Certificate : Bool :=
  allBoxesValid block384RightChunk000 &&
  coversFromBool block384RightChunk000 block384RightChunk000L block384RightChunk000R

theorem block384RightChunk000Certificate_eq_true :
    block384RightChunk000Certificate = true := by
  native_decide

def block384RightChainCertificate : Bool :=
  decide (
    block384RightL = ((17422109375000000033 : Rat) / 10000000000000000000) /\
    ((1071252511160714287 : Rat) / 390625000000000000) = block384RightR)

theorem block384RightChainCertificate_eq_true :
    block384RightChainCertificate = true := by
  native_decide

def block384LeftBoxCount : Nat := boxCount block384LeftBoxes
def block384RightBoxCount : Nat := 58

def block384_rational_certificate : Prop :=
    block384LeftCertificate = true /\
    block384RightChainCertificate = true /\
    block384RightChunk000Certificate = true

theorem block384_rational_certificate_proof :
    block384_rational_certificate := by
  exact ⟨block384LeftCertificate_eq_true, block384RightChainCertificate_eq_true, block384RightChunk000Certificate_eq_true⟩

end Block384
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block384

open Set

def block384W1 : Rat := ((8429180103914411 : Rat) / 10000000000000000)
def block384W2 : Rat := ((925197128691713 : Rat) / 20000000000000000)
def block384W3 : Rat := ((318738628916679 : Rat) / 2000000000000000)
def block384W4 : Rat := ((3518598311612653 : Rat) / 25000000000000000)
def block384S1 : Rat := ((18174751 : Rat) / 10000000)
def block384S2 : Rat := ((511587 : Rat) / 200000)
def block384S3 : Rat := ((26525340017857142867 : Rat) / 10000000000000000000)
def block384S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block384V (y : ℝ) : ℝ :=
  ratPotential block384W1 block384W2 block384W3 block384W4 block384S1 block384S2 block384S3 block384S4 y

def block384LeftParamsCertificate : Bool :=
  allBoxesSameParams block384LeftBoxes block384W1 block384W2 block384W3 block384W4 block384S1 block384S2 block384S3 block384S4

theorem block384LeftParamsCertificate_eq_true :
    block384LeftParamsCertificate = true := by
  native_decide

theorem block384_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block384LeftL : ℝ) (block384LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block384S1 : ℝ))
    (hy2ne : y ≠ (block384S2 : ℝ))
    (hy3ne : y ≠ (block384S3 : ℝ))
    (hy4ne : y ≠ (block384S4 : ℝ)) :
    0 < block384V y := by
  have hcert := block384LeftCertificate_eq_true
  unfold block384LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block384LeftBoxes) (lo := block384LeftL) (hi := block384LeftR)
    (w1 := block384W1) (w2 := block384W2) (w3 := block384W3) (w4 := block384W4)
    (s1 := block384S1) (s2 := block384S2) (s3 := block384S3) (s4 := block384S4)
    hboxes hcover block384LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block384RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block384RightChunk000 block384W1 block384W2 block384W3 block384W4 block384S1 block384S2 block384S3 block384S4

theorem block384RightChunk000ParamsCertificate_eq_true :
    block384RightChunk000ParamsCertificate = true := by
  native_decide

theorem block384_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block384RightChunk000L : ℝ) (block384RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block384S1 : ℝ))
    (hy2ne : y ≠ (block384S2 : ℝ))
    (hy3ne : y ≠ (block384S3 : ℝ))
    (hy4ne : y ≠ (block384S4 : ℝ)) :
    0 < block384V y := by
  have hcert := block384RightChunk000Certificate_eq_true
  unfold block384RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block384RightChunk000) (lo := block384RightChunk000L) (hi := block384RightChunk000R)
    (w1 := block384W1) (w2 := block384W2) (w3 := block384W3) (w4 := block384W4)
    (s1 := block384S1) (s2 := block384S2) (s3 := block384S3) (s4 := block384S4)
    hboxes hcover block384RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block384_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block384RightL : ℝ) (block384RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block384S1 : ℝ))
    (hy2ne : y ≠ (block384S2 : ℝ))
    (hy3ne : y ≠ (block384S3 : ℝ))
    (hy4ne : y ≠ (block384S4 : ℝ)) :
    0 < block384V y := by
  have hL : (block384RightChunk000L : ℝ) = (block384RightL : ℝ) := by
    norm_num [block384RightChunk000L, block384RightL]
  have hR : (block384RightChunk000R : ℝ) = (block384RightR : ℝ) := by
    norm_num [block384RightChunk000R, block384RightR]
  have hyc : y ∈ Icc (block384RightChunk000L : ℝ) (block384RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block384_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block384_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block384LeftL : ℝ) (block384LeftR : ℝ) →
    y ≠ 0 → y ≠ (block384S1 : ℝ) → y ≠ (block384S2 : ℝ) →
    y ≠ (block384S3 : ℝ) → y ≠ (block384S4 : ℝ) → 0 < block384V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block384RightL : ℝ) (block384RightR : ℝ) →
    y ≠ 0 → y ≠ (block384S1 : ℝ) → y ≠ (block384S2 : ℝ) →
    y ≠ (block384S3 : ℝ) → y ≠ (block384S4 : ℝ) → 0 < block384V y)

theorem block384_reallog_certificate_proof :
    block384_reallog_certificate := by
  exact ⟨block384_left_V_pos, block384_right_V_pos⟩

end Block384
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block384.block384V
#check Erdos1038Lean.M1817475.Block384.block384_left_V_pos
#check Erdos1038Lean.M1817475.Block384.block384_right_V_pos
#check Erdos1038Lean.M1817475.Block384.block384_reallog_certificate_proof
