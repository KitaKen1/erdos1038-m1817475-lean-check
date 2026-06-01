/-
Self-contained Lean4Web paste file.
Block 340 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block340

def block340LeftL : Rat := ((37540627232142857289 : Rat) / 50000000000000000000)
def block340LeftR : Rat := ((1877520089285714293 : Rat) / 2500000000000000000)
def block340RightL : Rat := ((87540627232142857289 : Rat) / 50000000000000000000)
def block340RightR : Rat := ((6877520089285714293 : Rat) / 2500000000000000000)

def block340LeftBoxes : List RatBox := [
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37540627232142857289 : Rat) / 50000000000000000000), R := ((1877520089285714293 : Rat) / 2500000000000000000), D0 := ((1877520089285714293 : Rat) / 2500000000000000000), D1 := ((53333127767857142711 : Rat) / 50000000000000000000), D2 := ((90356122767857142711 : Rat) / 50000000000000000000), D3 := ((47973116785714285647 : Rat) / 25000000000000000000), D4 := ((101077879196428566309 : Rat) / 50000000000000000000), LB := ((3183819853598037 : Rat) / 500000000000000000) }
]

def block340LeftCertificate : Bool :=
  allBoxesValid block340LeftBoxes &&
  coversFromBool block340LeftBoxes block340LeftL block340LeftR

theorem block340LeftCertificate_eq_true :
    block340LeftCertificate = true := by
  native_decide

def block340RightChunk000 : List RatBox := [
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87540627232142857289 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3333127767857142711 : Rat) / 50000000000000000000), D2 := ((40356122767857142711 : Rat) / 50000000000000000000), D3 := ((22973116785714285647 : Rat) / 25000000000000000000), D4 := ((51077879196428566309 : Rat) / 50000000000000000000), LB := ((9665097216761771 : Rat) / 5000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42613105803571428583 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((3647735933816843 : Rat) / 20000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24101608303571428583 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((5885768352952489 : Rat) / 50000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19473733928571428583 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((7777432371559133 : Rat) / 100000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17159796741071428583 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((3625894682995423 : Rat) / 200000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14845859553571428583 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((1088233077428653 : Rat) / 62500000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13688890959821428583 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((2579546962906451 : Rat) / 125000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((13110406662946428583 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((2990205301347637 : Rat) / 250000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12531922366071428583 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((871214082400601 : Rat) / 200000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11953438069196428583 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((8890653663898823 : Rat) / 1000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11664195920758928583 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((603109766690979 : Rat) / 100000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11374953772321428583 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((6990248635150853 : Rat) / 2000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11085711623883928583 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((6491957255820857 : Rat) / 5000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10796469475446428583 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((4821359195497643 : Rat) / 1000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10651848401227678583 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((1005416777492607 : Rat) / 250000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10507227327008928583 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((33194375670660137 : Rat) / 10000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10362606252790178583 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((2717775936417699 : Rat) / 1000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10217985178571428583 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((4440082364629283 : Rat) / 2000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10073364104352678583 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((571835940173333 : Rat) / 312500000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9928743030133928583 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((484761124903239 : Rat) / 312500000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9784121955915178583 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((6942184386624639 : Rat) / 5000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9639500881696428583 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((841371508846743 : Rat) / 625000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9494879807477678583 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((14296794375958377 : Rat) / 10000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9350258733258928583 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((822291365506031 : Rat) / 500000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9205637659040178583 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((19971907346387763 : Rat) / 10000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9061016584821428583 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((12472384017471333 : Rat) / 5000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8916395510602678583 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((31442114576845093 : Rat) / 10000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8771774436383928583 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((395509665069621 : Rat) / 100000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8627153362165178583 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((987386142876201 : Rat) / 200000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8482532287946428583 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((10420296780992433 : Rat) / 10000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8193290139508928583 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((1000927018321121 : Rat) / 250000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7904047991071428583 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((3935997533939653 : Rat) / 500000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7614805842633928583 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((12820223975153311 : Rat) / 1000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7325563694196428583 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1860933077953969 : Rat) / 200000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6747079397321428583 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((4297363965700421 : Rat) / 500000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028764110803571428583 : Rat) / 400000000000000000000), D0 := ((1028764110803571428583 : Rat) / 400000000000000000000), D1 := ((301774070803571428583 : Rat) / 400000000000000000000), D2 := ((5590110803571428583 : Rat) / 400000000000000000000), D3 := ((5590110803571428583 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((25668084262032473 : Rat) / 500000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028764110803571428583 : Rat) / 400000000000000000000), R := ((517177110803571428583 : Rat) / 200000000000000000000), D0 := ((517177110803571428583 : Rat) / 200000000000000000000), D1 := ((153682090803571428583 : Rat) / 200000000000000000000), D2 := ((5590110803571428583 : Rat) / 200000000000000000000), D3 := ((39130775625000000081 : Rat) / 400000000000000000000), D4 := ((80183940624999960201 : Rat) / 400000000000000000000), LB := ((24772748644202647 : Rat) / 1000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517177110803571428583 : Rat) / 200000000000000000000), R := ((1039944332410714285749 : Rat) / 400000000000000000000), D0 := ((1039944332410714285749 : Rat) / 400000000000000000000), D1 := ((312954292410714285749 : Rat) / 400000000000000000000), D2 := ((16770332410714285749 : Rat) / 400000000000000000000), D3 := ((16770332410714285749 : Rat) / 200000000000000000000), D4 := ((37296914910714265809 : Rat) / 200000000000000000000), LB := ((496483077357379 : Rat) / 31250000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1039944332410714285749 : Rat) / 400000000000000000000), R := ((261383610803571428583 : Rat) / 100000000000000000000), D0 := ((261383610803571428583 : Rat) / 100000000000000000000), D1 := ((79636100803571428583 : Rat) / 100000000000000000000), D2 := ((5590110803571428583 : Rat) / 100000000000000000000), D3 := ((5590110803571428583 : Rat) / 80000000000000000000), D4 := ((13800743803571420607 : Rat) / 80000000000000000000), LB := ((8905755260033399 : Rat) / 500000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261383610803571428583 : Rat) / 100000000000000000000), R := ((528357332410714285749 : Rat) / 200000000000000000000), D0 := ((528357332410714285749 : Rat) / 200000000000000000000), D1 := ((164862312410714285749 : Rat) / 200000000000000000000), D2 := ((16770332410714285749 : Rat) / 200000000000000000000), D3 := ((5590110803571428583 : Rat) / 100000000000000000000), D4 := ((15853402053571418613 : Rat) / 100000000000000000000), LB := ((17152889967220197 : Rat) / 100000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528357332410714285749 : Rat) / 200000000000000000000), R := ((133486860803571428583 : Rat) / 50000000000000000000), D0 := ((133486860803571428583 : Rat) / 50000000000000000000), D1 := ((42613105803571428583 : Rat) / 50000000000000000000), D2 := ((5590110803571428583 : Rat) / 50000000000000000000), D3 := ((5590110803571428583 : Rat) / 200000000000000000000), D4 := ((26116693303571408643 : Rat) / 200000000000000000000), LB := ((913181653390547 : Rat) / 12500000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133486860803571428583 : Rat) / 50000000000000000000), R := ((538010984196428571609 : Rat) / 200000000000000000000), D0 := ((538010984196428571609 : Rat) / 200000000000000000000), D1 := ((174515964196428571609 : Rat) / 200000000000000000000), D2 := ((26423984196428571609 : Rat) / 200000000000000000000), D3 := ((4063540982142857277 : Rat) / 200000000000000000000), D4 := ((1026329124999999003 : Rat) / 10000000000000000000), LB := ((5771735915896009 : Rat) / 50000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((538010984196428571609 : Rat) / 200000000000000000000), R := ((271037262589285714443 : Rat) / 100000000000000000000), D0 := ((271037262589285714443 : Rat) / 100000000000000000000), D1 := ((89289752589285714443 : Rat) / 100000000000000000000), D2 := ((15243762589285714443 : Rat) / 100000000000000000000), D3 := ((4063540982142857277 : Rat) / 100000000000000000000), D4 := ((16463041517857122783 : Rat) / 200000000000000000000), LB := ((175778149595599 : Rat) / 20000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((271037262589285714443 : Rat) / 100000000000000000000), R := ((2172361641696428572821 : Rat) / 800000000000000000000), D0 := ((2172361641696428572821 : Rat) / 800000000000000000000), D1 := ((718381561696428572821 : Rat) / 800000000000000000000), D2 := ((126013641696428572821 : Rat) / 800000000000000000000), D3 := ((36571868839285715493 : Rat) / 800000000000000000000), D4 := ((6199750267857132753 : Rat) / 100000000000000000000), LB := ((546405808292251 : Rat) / 25000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2172361641696428572821 : Rat) / 800000000000000000000), R := ((1088212591339285715049 : Rat) / 400000000000000000000), D0 := ((1088212591339285715049 : Rat) / 400000000000000000000), D1 := ((361222551339285715049 : Rat) / 400000000000000000000), D2 := ((65038591339285715049 : Rat) / 400000000000000000000), D3 := ((4063540982142857277 : Rat) / 80000000000000000000), D4 := ((45534461160714204747 : Rat) / 800000000000000000000), LB := ((1920497991194059 : Rat) / 200000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1088212591339285715049 : Rat) / 400000000000000000000), R := ((4356913906339285717473 : Rat) / 1600000000000000000000), D0 := ((4356913906339285717473 : Rat) / 1600000000000000000000), D1 := ((1448953746339285717473 : Rat) / 1600000000000000000000), D2 := ((264217906339285717473 : Rat) / 1600000000000000000000), D3 := ((85334360625000002817 : Rat) / 1600000000000000000000), D4 := ((4147092017857134747 : Rat) / 80000000000000000000), LB := ((2762410414462943 : Rat) / 250000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4356913906339285717473 : Rat) / 1600000000000000000000), R := ((17443909789285714299 : Rat) / 6400000000000000000), D0 := ((17443909789285714299 : Rat) / 6400000000000000000), D1 := ((5812069149285714299 : Rat) / 6400000000000000000), D2 := ((1073125789285714299 : Rat) / 6400000000000000000), D3 := ((44698950803571430047 : Rat) / 800000000000000000000), D4 := ((78878299374999837663 : Rat) / 1600000000000000000000), LB := ((3451336166657687 : Rat) / 500000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((17443909789285714299 : Rat) / 6400000000000000000), R := ((4365040988303571432027 : Rat) / 1600000000000000000000), D0 := ((4365040988303571432027 : Rat) / 1600000000000000000000), D1 := ((1457080828303571432027 : Rat) / 1600000000000000000000), D2 := ((272344988303571432027 : Rat) / 1600000000000000000000), D3 := ((93461442589285717371 : Rat) / 1600000000000000000000), D4 := ((37407379196428490193 : Rat) / 800000000000000000000), LB := ((2151500401429661 : Rat) / 625000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4365040988303571432027 : Rat) / 1600000000000000000000), R := ((546138066160714286163 : Rat) / 200000000000000000000), D0 := ((546138066160714286163 : Rat) / 200000000000000000000), D1 := ((182643046160714286163 : Rat) / 200000000000000000000), D2 := ((34551066160714286163 : Rat) / 200000000000000000000), D3 := ((12190622946428571831 : Rat) / 200000000000000000000), D4 := ((70751217410714123109 : Rat) / 1600000000000000000000), LB := ((6835480706879893 : Rat) / 10000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546138066160714286163 : Rat) / 200000000000000000000), R := ((1748454519910714287177 : Rat) / 640000000000000000000), D0 := ((1748454519910714287177 : Rat) / 640000000000000000000), D1 := ((585270455910714287177 : Rat) / 640000000000000000000), D2 := ((111376119910714287177 : Rat) / 640000000000000000000), D3 := ((199113508125000006573 : Rat) / 3200000000000000000000), D4 := ((8335959553571408229 : Rat) / 200000000000000000000), LB := ((1850394782861503 : Rat) / 500000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1748454519910714287177 : Rat) / 640000000000000000000), R := ((4373168070267857146581 : Rat) / 1600000000000000000000), D0 := ((4373168070267857146581 : Rat) / 1600000000000000000000), D1 := ((1465207910267857146581 : Rat) / 1600000000000000000000), D2 := ((280472070267857146581 : Rat) / 1600000000000000000000), D3 := ((4063540982142857277 : Rat) / 64000000000000000000), D4 := ((129311811874999674387 : Rat) / 3200000000000000000000), LB := ((2905151222590441 : Rat) / 1000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4373168070267857146581 : Rat) / 1600000000000000000000), R := ((8750399681517857150439 : Rat) / 3200000000000000000000), D0 := ((8750399681517857150439 : Rat) / 3200000000000000000000), D1 := ((2934479361517857150439 : Rat) / 3200000000000000000000), D2 := ((565007681517857150439 : Rat) / 3200000000000000000000), D3 := ((207240590089285721127 : Rat) / 3200000000000000000000), D4 := ((12524827089285681711 : Rat) / 320000000000000000000), LB := ((1154157921271881 : Rat) / 500000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8750399681517857150439 : Rat) / 3200000000000000000000), R := ((2188615805625000001929 : Rat) / 800000000000000000000), D0 := ((2188615805625000001929 : Rat) / 800000000000000000000), D1 := ((734635725625000001929 : Rat) / 800000000000000000000), D2 := ((142267805625000001929 : Rat) / 800000000000000000000), D3 := ((52826032767857144601 : Rat) / 800000000000000000000), D4 := ((121184729910713959833 : Rat) / 3200000000000000000000), LB := ((2396166076442871 : Rat) / 1250000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2188615805625000001929 : Rat) / 800000000000000000000), R := ((8758526763482142864993 : Rat) / 3200000000000000000000), D0 := ((8758526763482142864993 : Rat) / 3200000000000000000000), D1 := ((2942606443482142864993 : Rat) / 3200000000000000000000), D2 := ((573134763482142864993 : Rat) / 3200000000000000000000), D3 := ((215367672053571435681 : Rat) / 3200000000000000000000), D4 := ((29280297232142775639 : Rat) / 800000000000000000000), LB := ((17386995039333497 : Rat) / 10000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8758526763482142864993 : Rat) / 3200000000000000000000), R := ((876259030446428572227 : Rat) / 320000000000000000000), D0 := ((876259030446428572227 : Rat) / 320000000000000000000), D1 := ((294666998446428572227 : Rat) / 320000000000000000000), D2 := ((57719830446428572227 : Rat) / 320000000000000000000), D3 := ((109715606517857146479 : Rat) / 1600000000000000000000), D4 := ((113057647946428245279 : Rat) / 3200000000000000000000), LB := ((8912403291689297 : Rat) / 5000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((876259030446428572227 : Rat) / 320000000000000000000), R := ((8766653845446428579547 : Rat) / 3200000000000000000000), D0 := ((8766653845446428579547 : Rat) / 3200000000000000000000), D1 := ((2950733525446428579547 : Rat) / 3200000000000000000000), D2 := ((581261845446428579547 : Rat) / 3200000000000000000000), D3 := ((44698950803571430047 : Rat) / 640000000000000000000), D4 := ((54497053482142694001 : Rat) / 1600000000000000000000), LB := ((4116906736712611 : Rat) / 2000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8766653845446428579547 : Rat) / 3200000000000000000000), R := ((1096339673303571429603 : Rat) / 400000000000000000000), D0 := ((1096339673303571429603 : Rat) / 400000000000000000000), D1 := ((369349633303571429603 : Rat) / 400000000000000000000), D2 := ((73165673303571429603 : Rat) / 400000000000000000000), D3 := ((28444786875000000939 : Rat) / 400000000000000000000), D4 := ((4197222639285701229 : Rat) / 128000000000000000000), LB := ((25782812685754553 : Rat) / 10000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1096339673303571429603 : Rat) / 400000000000000000000), R := ((8774780927410714294101 : Rat) / 3200000000000000000000), D0 := ((8774780927410714294101 : Rat) / 3200000000000000000000), D1 := ((2958860607410714294101 : Rat) / 3200000000000000000000), D2 := ((589388927410714294101 : Rat) / 3200000000000000000000), D3 := ((231621835982142864789 : Rat) / 3200000000000000000000), D4 := ((12608378124999959181 : Rat) / 400000000000000000000), LB := ((3355325783986063 : Rat) / 1000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8774780927410714294101 : Rat) / 3200000000000000000000), R := ((4389422234196428575689 : Rat) / 1600000000000000000000), D0 := ((4389422234196428575689 : Rat) / 1600000000000000000000), D1 := ((1481462074196428575689 : Rat) / 1600000000000000000000), D2 := ((296726234196428575689 : Rat) / 1600000000000000000000), D3 := ((117842688482142861033 : Rat) / 1600000000000000000000), D4 := ((96803484017856816171 : Rat) / 3200000000000000000000), LB := ((4404902922387877 : Rat) / 1000000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4389422234196428575689 : Rat) / 1600000000000000000000), R := ((2196742887589285716483 : Rat) / 800000000000000000000), D0 := ((2196742887589285716483 : Rat) / 800000000000000000000), D1 := ((742762807589285716483 : Rat) / 800000000000000000000), D2 := ((150394887589285716483 : Rat) / 800000000000000000000), D3 := ((12190622946428571831 : Rat) / 160000000000000000000), D4 := ((46369971517856979447 : Rat) / 1600000000000000000000), LB := ((1543192353158987 : Rat) / 1250000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2196742887589285716483 : Rat) / 800000000000000000000), R := ((4397549316160714290243 : Rat) / 1600000000000000000000), D0 := ((4397549316160714290243 : Rat) / 1600000000000000000000), D1 := ((1489589156160714290243 : Rat) / 1600000000000000000000), D2 := ((304853316160714290243 : Rat) / 1600000000000000000000), D3 := ((125969770446428575587 : Rat) / 1600000000000000000000), D4 := ((4230643053571412217 : Rat) / 160000000000000000000), LB := ((495647535875271 : Rat) / 100000000000000000) },
  { w1 := ((2317912749508087 : Rat) / 2500000000000000), w2 := ((23740724542305587 : Rat) / 500000000000000000), w3 := ((730853464834767 : Rat) / 5000000000000000), w4 := ((6874268175946681 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133486860803571428583 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4397549316160714290243 : Rat) / 1600000000000000000000), R := ((6877520089285714293 : Rat) / 2500000000000000000), D0 := ((6877520089285714293 : Rat) / 2500000000000000000), D1 := ((2333832339285714293 : Rat) / 2500000000000000000), D2 := ((482682589285714293 : Rat) / 2500000000000000000), D3 := ((4063540982142857277 : Rat) / 50000000000000000000), D4 := ((38242889553571264893 : Rat) / 1600000000000000000000), LB := ((5060521797996653 : Rat) / 500000000000000000) }
]

def block340RightChunk000L : Rat := ((87540627232142857289 : Rat) / 50000000000000000000)
def block340RightChunk000R : Rat := ((6877520089285714293 : Rat) / 2500000000000000000)

def block340RightChunk000Certificate : Bool :=
  allBoxesValid block340RightChunk000 &&
  coversFromBool block340RightChunk000 block340RightChunk000L block340RightChunk000R

theorem block340RightChunk000Certificate_eq_true :
    block340RightChunk000Certificate = true := by
  native_decide

def block340RightChainCertificate : Bool :=
  decide (
    block340RightL = ((87540627232142857289 : Rat) / 50000000000000000000) /\
    ((6877520089285714293 : Rat) / 2500000000000000000) = block340RightR)

theorem block340RightChainCertificate_eq_true :
    block340RightChainCertificate = true := by
  native_decide

def block340LeftBoxCount : Nat := boxCount block340LeftBoxes
def block340RightBoxCount : Nat := 62

def block340_rational_certificate : Prop :=
    block340LeftCertificate = true /\
    block340RightChainCertificate = true /\
    block340RightChunk000Certificate = true

theorem block340_rational_certificate_proof :
    block340_rational_certificate := by
  exact ⟨block340LeftCertificate_eq_true, block340RightChainCertificate_eq_true, block340RightChunk000Certificate_eq_true⟩

end Block340
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block340

open Set

def block340W1 : Rat := ((2317912749508087 : Rat) / 2500000000000000)
def block340W2 : Rat := ((23740724542305587 : Rat) / 500000000000000000)
def block340W3 : Rat := ((730853464834767 : Rat) / 5000000000000000)
def block340W4 : Rat := ((6874268175946681 : Rat) / 50000000000000000)
def block340S1 : Rat := ((18174751 : Rat) / 10000000)
def block340S2 : Rat := ((511587 : Rat) / 200000)
def block340S3 : Rat := ((133486860803571428583 : Rat) / 50000000000000000000)
def block340S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block340V (y : ℝ) : ℝ :=
  ratPotential block340W1 block340W2 block340W3 block340W4 block340S1 block340S2 block340S3 block340S4 y

def block340LeftParamsCertificate : Bool :=
  allBoxesSameParams block340LeftBoxes block340W1 block340W2 block340W3 block340W4 block340S1 block340S2 block340S3 block340S4

theorem block340LeftParamsCertificate_eq_true :
    block340LeftParamsCertificate = true := by
  native_decide

theorem block340_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block340LeftL : ℝ) (block340LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block340S1 : ℝ))
    (hy2ne : y ≠ (block340S2 : ℝ))
    (hy3ne : y ≠ (block340S3 : ℝ))
    (hy4ne : y ≠ (block340S4 : ℝ)) :
    0 < block340V y := by
  have hcert := block340LeftCertificate_eq_true
  unfold block340LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block340LeftBoxes) (lo := block340LeftL) (hi := block340LeftR)
    (w1 := block340W1) (w2 := block340W2) (w3 := block340W3) (w4 := block340W4)
    (s1 := block340S1) (s2 := block340S2) (s3 := block340S3) (s4 := block340S4)
    hboxes hcover block340LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block340RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block340RightChunk000 block340W1 block340W2 block340W3 block340W4 block340S1 block340S2 block340S3 block340S4

theorem block340RightChunk000ParamsCertificate_eq_true :
    block340RightChunk000ParamsCertificate = true := by
  native_decide

theorem block340_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block340RightChunk000L : ℝ) (block340RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block340S1 : ℝ))
    (hy2ne : y ≠ (block340S2 : ℝ))
    (hy3ne : y ≠ (block340S3 : ℝ))
    (hy4ne : y ≠ (block340S4 : ℝ)) :
    0 < block340V y := by
  have hcert := block340RightChunk000Certificate_eq_true
  unfold block340RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block340RightChunk000) (lo := block340RightChunk000L) (hi := block340RightChunk000R)
    (w1 := block340W1) (w2 := block340W2) (w3 := block340W3) (w4 := block340W4)
    (s1 := block340S1) (s2 := block340S2) (s3 := block340S3) (s4 := block340S4)
    hboxes hcover block340RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block340_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block340RightL : ℝ) (block340RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block340S1 : ℝ))
    (hy2ne : y ≠ (block340S2 : ℝ))
    (hy3ne : y ≠ (block340S3 : ℝ))
    (hy4ne : y ≠ (block340S4 : ℝ)) :
    0 < block340V y := by
  have hL : (block340RightChunk000L : ℝ) = (block340RightL : ℝ) := by
    norm_num [block340RightChunk000L, block340RightL]
  have hR : (block340RightChunk000R : ℝ) = (block340RightR : ℝ) := by
    norm_num [block340RightChunk000R, block340RightR]
  have hyc : y ∈ Icc (block340RightChunk000L : ℝ) (block340RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block340_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block340_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block340LeftL : ℝ) (block340LeftR : ℝ) →
    y ≠ 0 → y ≠ (block340S1 : ℝ) → y ≠ (block340S2 : ℝ) →
    y ≠ (block340S3 : ℝ) → y ≠ (block340S4 : ℝ) → 0 < block340V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block340RightL : ℝ) (block340RightR : ℝ) →
    y ≠ 0 → y ≠ (block340S1 : ℝ) → y ≠ (block340S2 : ℝ) →
    y ≠ (block340S3 : ℝ) → y ≠ (block340S4 : ℝ) → 0 < block340V y)

theorem block340_reallog_certificate_proof :
    block340_reallog_certificate := by
  exact ⟨block340_left_V_pos, block340_right_V_pos⟩

end Block340
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block340.block340V
#check Erdos1038Lean.M1817475.Block340.block340_left_V_pos
#check Erdos1038Lean.M1817475.Block340.block340_right_V_pos
#check Erdos1038Lean.M1817475.Block340.block340_reallog_certificate_proof
