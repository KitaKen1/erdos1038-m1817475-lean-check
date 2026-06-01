/-
Self-contained Lean4Web paste file.
Block 95 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block095

def block095LeftL : Rat := ((1247981026785714287 : Rat) / 1562500000000000000)
def block095LeftR : Rat := ((7989033482142857151 : Rat) / 10000000000000000000)
def block095RightL : Rat := ((2810481026785714287 : Rat) / 1562500000000000000)
def block095RightR : Rat := ((27989033482142857151 : Rat) / 10000000000000000000)

def block095LeftBoxes : List RatBox := [
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1247981026785714287 : Rat) / 1562500000000000000), R := ((7989033482142857151 : Rat) / 10000000000000000000), D0 := ((7989033482142857151 : Rat) / 10000000000000000000), D1 := ((1591823816964285713 : Rat) / 1562500000000000000), D2 := ((2748792410714285713 : Rat) / 1562500000000000000), D3 := ((95389084017857142747 : Rat) / 50000000000000000000), D4 := ((12411141986607142227 : Rat) / 6250000000000000000), LB := ((754595712584287 : Rat) / 125000000000000000) }
]

def block095LeftCertificate : Bool :=
  allBoxesValid block095LeftBoxes &&
  coversFromBool block095LeftBoxes block095LeftL block095LeftR

theorem block095LeftCertificate_eq_true :
    block095LeftCertificate = true := by
  native_decide

def block095RightChunk000 : List RatBox := [
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2810481026785714287 : Rat) / 1562500000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((29323816964285713 : Rat) / 1562500000000000000), D2 := ((1186292410714285713 : Rat) / 1562500000000000000), D3 := ((45389084017857142747 : Rat) / 50000000000000000000), D4 := ((6161141986607142227 : Rat) / 6250000000000000000), LB := ((3978748272403983 : Rat) / 500000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((44450721874999999931 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((13674546995067747 : Rat) / 10000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((25939224374999999931 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((341201263846887 : Rat) / 625000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((16683475624999999931 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((697716845072937 : Rat) / 2500000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((12055601249999999931 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((27184008156355993 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((519014726874999999931 : Rat) / 200000000000000000000), D0 := ((519014726874999999931 : Rat) / 200000000000000000000), D1 := ((155519706874999999931 : Rat) / 200000000000000000000), D2 := ((7427726874999999931 : Rat) / 200000000000000000000), D3 := ((7427726874999999931 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((37815324241438353 : Rat) / 5000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((519014726874999999931 : Rat) / 200000000000000000000), R := ((1045457180624999999793 : Rat) / 400000000000000000000), D0 := ((1045457180624999999793 : Rat) / 400000000000000000000), D1 := ((318467140624999999793 : Rat) / 400000000000000000000), D2 := ((22283180624999999793 : Rat) / 400000000000000000000), D3 := ((22283180624999999793 : Rat) / 200000000000000000000), D4 := ((37883388124999980069 : Rat) / 200000000000000000000), LB := ((2141198677585443 : Rat) / 500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1045457180624999999793 : Rat) / 400000000000000000000), R := ((2098342088124999999517 : Rat) / 800000000000000000000), D0 := ((2098342088124999999517 : Rat) / 800000000000000000000), D1 := ((644362008124999999517 : Rat) / 800000000000000000000), D2 := ((51994088124999999517 : Rat) / 800000000000000000000), D3 := ((7427726874999999931 : Rat) / 80000000000000000000), D4 := ((68339049374999960207 : Rat) / 400000000000000000000), LB := ((4187743153990703 : Rat) / 500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2098342088124999999517 : Rat) / 800000000000000000000), R := ((840822380624999999793 : Rat) / 320000000000000000000), D0 := ((840822380624999999793 : Rat) / 320000000000000000000), D1 := ((259230348624999999793 : Rat) / 320000000000000000000), D2 := ((22283180624999999793 : Rat) / 320000000000000000000), D3 := ((66849541874999999379 : Rat) / 800000000000000000000), D4 := ((129250371874999920483 : Rat) / 800000000000000000000), LB := ((6165795493738191 : Rat) / 500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((840822380624999999793 : Rat) / 320000000000000000000), R := ((263221226874999999931 : Rat) / 100000000000000000000), D0 := ((263221226874999999931 : Rat) / 100000000000000000000), D1 := ((81473716874999999931 : Rat) / 100000000000000000000), D2 := ((7427726874999999931 : Rat) / 100000000000000000000), D3 := ((126271356874999998827 : Rat) / 1600000000000000000000), D4 := ((50214603374999968207 : Rat) / 320000000000000000000), LB := ((7862525169135437 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((263221226874999999931 : Rat) / 100000000000000000000), R := ((4218967356874999998827 : Rat) / 1600000000000000000000), D0 := ((4218967356874999998827 : Rat) / 1600000000000000000000), D1 := ((1311007196874999998827 : Rat) / 1600000000000000000000), D2 := ((126271356874999998827 : Rat) / 1600000000000000000000), D3 := ((7427726874999999931 : Rat) / 100000000000000000000), D4 := ((15227830624999990069 : Rat) / 100000000000000000000), LB := ((1935688610258779 : Rat) / 500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4218967356874999998827 : Rat) / 1600000000000000000000), R := ((2113197541874999999379 : Rat) / 800000000000000000000), D0 := ((2113197541874999999379 : Rat) / 800000000000000000000), D1 := ((659217461874999999379 : Rat) / 800000000000000000000), D2 := ((66849541874999999379 : Rat) / 800000000000000000000), D3 := ((22283180624999999793 : Rat) / 320000000000000000000), D4 := ((236217563124999841173 : Rat) / 1600000000000000000000), LB := ((159223617767279 : Rat) / 400000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2113197541874999999379 : Rat) / 800000000000000000000), R := ((8460217894374999997447 : Rat) / 3200000000000000000000), D0 := ((8460217894374999997447 : Rat) / 3200000000000000000000), D1 := ((2644297574374999997447 : Rat) / 3200000000000000000000), D2 := ((274825894374999997447 : Rat) / 3200000000000000000000), D3 := ((51994088124999999517 : Rat) / 800000000000000000000), D4 := ((114394918124999920621 : Rat) / 800000000000000000000), LB := ((4396706701999653 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8460217894374999997447 : Rat) / 3200000000000000000000), R := ((4233822810624999998689 : Rat) / 1600000000000000000000), D0 := ((4233822810624999998689 : Rat) / 1600000000000000000000), D1 := ((1325862650624999998689 : Rat) / 1600000000000000000000), D2 := ((141126810624999998689 : Rat) / 1600000000000000000000), D3 := ((200548625624999998137 : Rat) / 3200000000000000000000), D4 := ((450151945624999682553 : Rat) / 3200000000000000000000), LB := ((1576993866189591 : Rat) / 500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4233822810624999998689 : Rat) / 1600000000000000000000), R := ((8475073348124999997309 : Rat) / 3200000000000000000000), D0 := ((8475073348124999997309 : Rat) / 3200000000000000000000), D1 := ((2659153028124999997309 : Rat) / 3200000000000000000000), D2 := ((289681348124999997309 : Rat) / 3200000000000000000000), D3 := ((96560449374999999103 : Rat) / 1600000000000000000000), D4 := ((221362109374999841311 : Rat) / 1600000000000000000000), LB := ((2074627560631259 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8475073348124999997309 : Rat) / 3200000000000000000000), R := ((212062526874999999931 : Rat) / 80000000000000000000), D0 := ((212062526874999999931 : Rat) / 80000000000000000000), D1 := ((66664518874999999931 : Rat) / 80000000000000000000), D2 := ((7427726874999999931 : Rat) / 80000000000000000000), D3 := ((7427726874999999931 : Rat) / 128000000000000000000), D4 := ((435296491874999682691 : Rat) / 3200000000000000000000), LB := ((5837849728087263 : Rat) / 5000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((212062526874999999931 : Rat) / 80000000000000000000), R := ((8489928801874999997171 : Rat) / 3200000000000000000000), D0 := ((8489928801874999997171 : Rat) / 3200000000000000000000), D1 := ((2674008481874999997171 : Rat) / 3200000000000000000000), D2 := ((304536801874999997171 : Rat) / 3200000000000000000000), D3 := ((22283180624999999793 : Rat) / 400000000000000000000), D4 := ((10696719124999992069 : Rat) / 80000000000000000000), LB := ((2213690724988393 : Rat) / 5000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8489928801874999997171 : Rat) / 3200000000000000000000), R := ((16987285330624999994273 : Rat) / 6400000000000000000000), D0 := ((16987285330624999994273 : Rat) / 6400000000000000000000), D1 := ((5355444690624999994273 : Rat) / 6400000000000000000000), D2 := ((616501330624999994273 : Rat) / 6400000000000000000000), D3 := ((170837718124999998413 : Rat) / 3200000000000000000000), D4 := ((420441038124999682829 : Rat) / 3200000000000000000000), LB := ((33275270445336513 : Rat) / 10000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16987285330624999994273 : Rat) / 6400000000000000000000), R := ((4248678264374999998551 : Rat) / 1600000000000000000000), D0 := ((4248678264374999998551 : Rat) / 1600000000000000000000), D1 := ((1340718104374999998551 : Rat) / 1600000000000000000000), D2 := ((155982264374999998551 : Rat) / 1600000000000000000000), D3 := ((66849541874999999379 : Rat) / 1280000000000000000000), D4 := ((833454349374999365727 : Rat) / 6400000000000000000000), LB := ((15668676156381789 : Rat) / 5000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4248678264374999998551 : Rat) / 1600000000000000000000), R := ((3400428156874999998827 : Rat) / 1280000000000000000000), D0 := ((3400428156874999998827 : Rat) / 1280000000000000000000), D1 := ((1074060028874999998827 : Rat) / 1280000000000000000000), D2 := ((126271356874999998827 : Rat) / 1280000000000000000000), D3 := ((81704995624999999241 : Rat) / 1600000000000000000000), D4 := ((206506655624999841449 : Rat) / 1600000000000000000000), LB := ((2993037960801803 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3400428156874999998827 : Rat) / 1280000000000000000000), R := ((8504784255624999997033 : Rat) / 3200000000000000000000), D0 := ((8504784255624999997033 : Rat) / 3200000000000000000000), D1 := ((2688863935624999997033 : Rat) / 3200000000000000000000), D2 := ((319392255624999997033 : Rat) / 3200000000000000000000), D3 := ((319392255624999997033 : Rat) / 6400000000000000000000), D4 := ((163719779124999873173 : Rat) / 1280000000000000000000), LB := ((1453614876432141 : Rat) / 500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8504784255624999997033 : Rat) / 3200000000000000000000), R := ((17016996238124999993997 : Rat) / 6400000000000000000000), D0 := ((17016996238124999993997 : Rat) / 6400000000000000000000), D1 := ((5385155598124999993997 : Rat) / 6400000000000000000000), D2 := ((646212238124999993997 : Rat) / 6400000000000000000000), D3 := ((155982264374999998551 : Rat) / 3200000000000000000000), D4 := ((405585584374999682967 : Rat) / 3200000000000000000000), LB := ((89944389200243 : Rat) / 31250000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17016996238124999993997 : Rat) / 6400000000000000000000), R := ((2128052995624999999241 : Rat) / 800000000000000000000), D0 := ((2128052995624999999241 : Rat) / 800000000000000000000), D1 := ((674072915624999999241 : Rat) / 800000000000000000000), D2 := ((81704995624999999241 : Rat) / 800000000000000000000), D3 := ((304536801874999997171 : Rat) / 6400000000000000000000), D4 := ((803743441874999366003 : Rat) / 6400000000000000000000), LB := ((29080458922322583 : Rat) / 10000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2128052995624999999241 : Rat) / 800000000000000000000), R := ((17031851691874999993859 : Rat) / 6400000000000000000000), D0 := ((17031851691874999993859 : Rat) / 6400000000000000000000), D1 := ((5400011051874999993859 : Rat) / 6400000000000000000000), D2 := ((661067691874999993859 : Rat) / 6400000000000000000000), D3 := ((7427726874999999931 : Rat) / 160000000000000000000), D4 := ((99539464374999920759 : Rat) / 800000000000000000000), LB := ((2998879819267053 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17031851691874999993859 : Rat) / 6400000000000000000000), R := ((1703927941874999999379 : Rat) / 640000000000000000000), D0 := ((1703927941874999999379 : Rat) / 640000000000000000000), D1 := ((540743877874999999379 : Rat) / 640000000000000000000), D2 := ((66849541874999999379 : Rat) / 640000000000000000000), D3 := ((289681348124999997309 : Rat) / 6400000000000000000000), D4 := ((788887988124999366141 : Rat) / 6400000000000000000000), LB := ((788261837449511 : Rat) / 250000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1703927941874999999379 : Rat) / 640000000000000000000), R := ((17046707145624999993721 : Rat) / 6400000000000000000000), D0 := ((17046707145624999993721 : Rat) / 6400000000000000000000), D1 := ((5414866505624999993721 : Rat) / 6400000000000000000000), D2 := ((675923145624999993721 : Rat) / 6400000000000000000000), D3 := ((141126810624999998689 : Rat) / 3200000000000000000000), D4 := ((78146026124999936621 : Rat) / 640000000000000000000), LB := ((3373040114341419 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17046707145624999993721 : Rat) / 6400000000000000000000), R := ((4263533718124999998413 : Rat) / 1600000000000000000000), D0 := ((4263533718124999998413 : Rat) / 1600000000000000000000), D1 := ((1355573558124999998413 : Rat) / 1600000000000000000000), D2 := ((170837718124999998413 : Rat) / 1600000000000000000000), D3 := ((274825894374999997447 : Rat) / 6400000000000000000000), D4 := ((774032534374999366279 : Rat) / 6400000000000000000000), LB := ((36615334079500017 : Rat) / 10000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4263533718124999998413 : Rat) / 1600000000000000000000), R := ((8534495163124999996757 : Rat) / 3200000000000000000000), D0 := ((8534495163124999996757 : Rat) / 3200000000000000000000), D1 := ((2718574843124999996757 : Rat) / 3200000000000000000000), D2 := ((349103163124999996757 : Rat) / 3200000000000000000000), D3 := ((66849541874999999379 : Rat) / 1600000000000000000000), D4 := ((191651201874999841587 : Rat) / 1600000000000000000000), LB := ((6477001496201229 : Rat) / 10000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8534495163124999996757 : Rat) / 3200000000000000000000), R := ((533870180624999999793 : Rat) / 200000000000000000000), D0 := ((533870180624999999793 : Rat) / 200000000000000000000), D1 := ((170375160624999999793 : Rat) / 200000000000000000000), D2 := ((22283180624999999793 : Rat) / 200000000000000000000), D3 := ((126271356874999998827 : Rat) / 3200000000000000000000), D4 := ((375874676874999683243 : Rat) / 3200000000000000000000), LB := ((801318880764873 : Rat) / 500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((533870180624999999793 : Rat) / 200000000000000000000), R := ((8549350616874999996619 : Rat) / 3200000000000000000000), D0 := ((8549350616874999996619 : Rat) / 3200000000000000000000), D1 := ((2733430296874999996619 : Rat) / 3200000000000000000000), D2 := ((363958616874999996619 : Rat) / 3200000000000000000000), D3 := ((7427726874999999931 : Rat) / 200000000000000000000), D4 := ((23027934374999980207 : Rat) / 200000000000000000000), LB := ((3604661948926613 : Rat) / 1250000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8549350616874999996619 : Rat) / 3200000000000000000000), R := ((171135566874999999931 : Rat) / 64000000000000000000), D0 := ((171135566874999999931 : Rat) / 64000000000000000000), D1 := ((54817160474999999931 : Rat) / 64000000000000000000), D2 := ((7427726874999999931 : Rat) / 64000000000000000000), D3 := ((22283180624999999793 : Rat) / 640000000000000000000), D4 := ((361019223124999683381 : Rat) / 3200000000000000000000), LB := ((2262024149893349 : Rat) / 500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((171135566874999999931 : Rat) / 64000000000000000000), R := ((8564206070624999996481 : Rat) / 3200000000000000000000), D0 := ((8564206070624999996481 : Rat) / 3200000000000000000000), D1 := ((2748285750624999996481 : Rat) / 3200000000000000000000), D2 := ((378814070624999996481 : Rat) / 3200000000000000000000), D3 := ((51994088124999999517 : Rat) / 1600000000000000000000), D4 := ((7071829924999993669 : Rat) / 64000000000000000000), LB := ((205096379046827 : Rat) / 31250000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8564206070624999996481 : Rat) / 3200000000000000000000), R := ((2142908449374999999103 : Rat) / 800000000000000000000), D0 := ((2142908449374999999103 : Rat) / 800000000000000000000), D1 := ((688928369374999999103 : Rat) / 800000000000000000000), D2 := ((96560449374999999103 : Rat) / 800000000000000000000), D3 := ((96560449374999999103 : Rat) / 3200000000000000000000), D4 := ((346163769374999683519 : Rat) / 3200000000000000000000), LB := ((2262152043630089 : Rat) / 250000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2142908449374999999103 : Rat) / 800000000000000000000), R := ((4293244625624999998137 : Rat) / 1600000000000000000000), D0 := ((4293244625624999998137 : Rat) / 1600000000000000000000), D1 := ((1385284465624999998137 : Rat) / 1600000000000000000000), D2 := ((200548625624999998137 : Rat) / 1600000000000000000000), D3 := ((22283180624999999793 : Rat) / 800000000000000000000), D4 := ((84684010624999920897 : Rat) / 800000000000000000000), LB := ((1080688683086739 : Rat) / 200000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4293244625624999998137 : Rat) / 1600000000000000000000), R := ((1075168088124999999517 : Rat) / 400000000000000000000), D0 := ((1075168088124999999517 : Rat) / 400000000000000000000), D1 := ((348178048124999999517 : Rat) / 400000000000000000000), D2 := ((51994088124999999517 : Rat) / 400000000000000000000), D3 := ((7427726874999999931 : Rat) / 320000000000000000000), D4 := ((161940294374999841863 : Rat) / 1600000000000000000000), LB := ((827862631970263 : Rat) / 62500000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1075168088124999999517 : Rat) / 400000000000000000000), R := ((431552780624999999793 : Rat) / 160000000000000000000), D0 := ((431552780624999999793 : Rat) / 160000000000000000000), D1 := ((140756764624999999793 : Rat) / 160000000000000000000), D2 := ((22283180624999999793 : Rat) / 160000000000000000000), D3 := ((7427726874999999931 : Rat) / 400000000000000000000), D4 := ((38628141874999960483 : Rat) / 400000000000000000000), LB := ((2241896126901033 : Rat) / 200000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((431552780624999999793 : Rat) / 160000000000000000000), R := ((135324476874999999931 : Rat) / 50000000000000000000), D0 := ((135324476874999999931 : Rat) / 50000000000000000000), D1 := ((44450721874999999931 : Rat) / 50000000000000000000), D2 := ((7427726874999999931 : Rat) / 50000000000000000000), D3 := ((7427726874999999931 : Rat) / 800000000000000000000), D4 := ((13965711374999984207 : Rat) / 160000000000000000000), LB := ((1289366203806007 : Rat) / 25000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((135324476874999999931 : Rat) / 50000000000000000000), R := ((1086495866874999994517 : Rat) / 400000000000000000000), D0 := ((1086495866874999994517 : Rat) / 400000000000000000000), D1 := ((359505826874999994517 : Rat) / 400000000000000000000), D2 := ((63321866874999994517 : Rat) / 400000000000000000000), D3 := ((3900051874999995069 : Rat) / 400000000000000000000), D4 := ((3900051874999995069 : Rat) / 50000000000000000000), LB := ((4342592049633859 : Rat) / 100000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1086495866874999994517 : Rat) / 400000000000000000000), R := ((2176891785624999984103 : Rat) / 800000000000000000000), D0 := ((2176891785624999984103 : Rat) / 800000000000000000000), D1 := ((722911705624999984103 : Rat) / 800000000000000000000), D2 := ((130543785624999984103 : Rat) / 800000000000000000000), D3 := ((11700155624999985207 : Rat) / 800000000000000000000), D4 := ((27300363124999965483 : Rat) / 400000000000000000000), LB := ((3644236001217209 : Rat) / 125000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2176891785624999984103 : Rat) / 800000000000000000000), R := ((545197959374999994793 : Rat) / 200000000000000000000), D0 := ((545197959374999994793 : Rat) / 200000000000000000000), D1 := ((181702939374999994793 : Rat) / 200000000000000000000), D2 := ((33610959374999994793 : Rat) / 200000000000000000000), D3 := ((3900051874999995069 : Rat) / 200000000000000000000), D4 := ((50700674374999935897 : Rat) / 800000000000000000000), LB := ((11109992870541041 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((545197959374999994793 : Rat) / 200000000000000000000), R := ((4365483726874999953413 : Rat) / 1600000000000000000000), D0 := ((4365483726874999953413 : Rat) / 1600000000000000000000), D1 := ((1457523566874999953413 : Rat) / 1600000000000000000000), D2 := ((272787726874999953413 : Rat) / 1600000000000000000000), D3 := ((35100466874999955621 : Rat) / 1600000000000000000000), D4 := ((11700155624999985207 : Rat) / 200000000000000000000), LB := ((308283250196123 : Rat) / 25000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4365483726874999953413 : Rat) / 1600000000000000000000), R := ((2184691889374999974241 : Rat) / 800000000000000000000), D0 := ((2184691889374999974241 : Rat) / 800000000000000000000), D1 := ((730711809374999974241 : Rat) / 800000000000000000000), D2 := ((138343889374999974241 : Rat) / 800000000000000000000), D3 := ((3900051874999995069 : Rat) / 160000000000000000000), D4 := ((89701193124999886587 : Rat) / 1600000000000000000000), LB := ((3507637614025949 : Rat) / 500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2184691889374999974241 : Rat) / 800000000000000000000), R := ((4373283830624999943551 : Rat) / 1600000000000000000000), D0 := ((4373283830624999943551 : Rat) / 1600000000000000000000), D1 := ((1465323670624999943551 : Rat) / 1600000000000000000000), D2 := ((280587830624999943551 : Rat) / 1600000000000000000000), D3 := ((42900570624999945759 : Rat) / 1600000000000000000000), D4 := ((42900570624999945759 : Rat) / 800000000000000000000), LB := ((2762247751956437 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4373283830624999943551 : Rat) / 1600000000000000000000), R := ((8750467713124999882171 : Rat) / 3200000000000000000000), D0 := ((8750467713124999882171 : Rat) / 3200000000000000000000), D1 := ((2934547393124999882171 : Rat) / 3200000000000000000000), D2 := ((565075713124999882171 : Rat) / 3200000000000000000000), D3 := ((89701193124999886587 : Rat) / 3200000000000000000000), D4 := ((81901089374999896449 : Rat) / 1600000000000000000000), LB := ((352760424240553 : Rat) / 62500000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8750467713124999882171 : Rat) / 3200000000000000000000), R := ((218859194124999996931 : Rat) / 80000000000000000000), D0 := ((218859194124999996931 : Rat) / 80000000000000000000), D1 := ((73461186124999996931 : Rat) / 80000000000000000000), D2 := ((14224394124999996931 : Rat) / 80000000000000000000), D3 := ((11700155624999985207 : Rat) / 400000000000000000000), D4 := ((159902126874999797829 : Rat) / 3200000000000000000000), LB := ((4238245288906817 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((218859194124999996931 : Rat) / 80000000000000000000), R := ((8758267816874999872309 : Rat) / 3200000000000000000000), D0 := ((8758267816874999872309 : Rat) / 3200000000000000000000), D1 := ((2942347496874999872309 : Rat) / 3200000000000000000000), D2 := ((572875816874999872309 : Rat) / 3200000000000000000000), D3 := ((3900051874999995069 : Rat) / 128000000000000000000), D4 := ((3900051874999995069 : Rat) / 80000000000000000000), LB := ((7675282657139959 : Rat) / 2500000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8758267816874999872309 : Rat) / 3200000000000000000000), R := ((4381083934374999933689 : Rat) / 1600000000000000000000), D0 := ((4381083934374999933689 : Rat) / 1600000000000000000000), D1 := ((1473123774374999933689 : Rat) / 1600000000000000000000), D2 := ((288387934374999933689 : Rat) / 1600000000000000000000), D3 := ((50700674374999935897 : Rat) / 1600000000000000000000), D4 := ((152102023124999807691 : Rat) / 3200000000000000000000), LB := ((4273109199662839 : Rat) / 2000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4381083934374999933689 : Rat) / 1600000000000000000000), R := ((8766067920624999862447 : Rat) / 3200000000000000000000), D0 := ((8766067920624999862447 : Rat) / 3200000000000000000000), D1 := ((2950147600624999862447 : Rat) / 3200000000000000000000), D2 := ((580675920624999862447 : Rat) / 3200000000000000000000), D3 := ((105301400624999866863 : Rat) / 3200000000000000000000), D4 := ((74100985624999906311 : Rat) / 1600000000000000000000), LB := ((57434117134747 : Rat) / 40000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8766067920624999862447 : Rat) / 3200000000000000000000), R := ((2192491993124999964379 : Rat) / 800000000000000000000), D0 := ((2192491993124999964379 : Rat) / 800000000000000000000), D1 := ((738511913124999964379 : Rat) / 800000000000000000000), D2 := ((146143993124999964379 : Rat) / 800000000000000000000), D3 := ((27300363124999965483 : Rat) / 800000000000000000000), D4 := ((144301919374999817553 : Rat) / 3200000000000000000000), LB := ((9676882741062043 : Rat) / 10000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2192491993124999964379 : Rat) / 800000000000000000000), R := ((1754773604874999970517 : Rat) / 640000000000000000000), D0 := ((1754773604874999970517 : Rat) / 640000000000000000000), D1 := ((591589540874999970517 : Rat) / 640000000000000000000), D2 := ((117695204874999970517 : Rat) / 640000000000000000000), D3 := ((113101504374999857001 : Rat) / 3200000000000000000000), D4 := ((35100466874999955621 : Rat) / 800000000000000000000), LB := ((3665349717398847 : Rat) / 5000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1754773604874999970517 : Rat) / 640000000000000000000), R := ((4388884038124999923827 : Rat) / 1600000000000000000000), D0 := ((4388884038124999923827 : Rat) / 1600000000000000000000), D1 := ((1480923878124999923827 : Rat) / 1600000000000000000000), D2 := ((296188038124999923827 : Rat) / 1600000000000000000000), D3 := ((11700155624999985207 : Rat) / 320000000000000000000), D4 := ((27300363124999965483 : Rat) / 640000000000000000000), LB := ((3671485964811261 : Rat) / 5000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4388884038124999923827 : Rat) / 1600000000000000000000), R := ((8781668128124999842723 : Rat) / 3200000000000000000000), D0 := ((8781668128124999842723 : Rat) / 3200000000000000000000), D1 := ((2965747808124999842723 : Rat) / 3200000000000000000000), D2 := ((596276128124999842723 : Rat) / 3200000000000000000000), D3 := ((120901608124999847139 : Rat) / 3200000000000000000000), D4 := ((66300881874999916173 : Rat) / 1600000000000000000000), LB := ((1949892624946381 : Rat) / 2000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8781668128124999842723 : Rat) / 3200000000000000000000), R := ((274549005624999994931 : Rat) / 100000000000000000000), D0 := ((274549005624999994931 : Rat) / 100000000000000000000), D1 := ((92801495624999994931 : Rat) / 100000000000000000000), D2 := ((18755505624999994931 : Rat) / 100000000000000000000), D3 := ((3900051874999995069 : Rat) / 100000000000000000000), D4 := ((128701711874999837277 : Rat) / 3200000000000000000000), LB := ((14598823615206147 : Rat) / 10000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((274549005624999994931 : Rat) / 100000000000000000000), R := ((8789468231874999832861 : Rat) / 3200000000000000000000), D0 := ((8789468231874999832861 : Rat) / 3200000000000000000000), D1 := ((2973547911874999832861 : Rat) / 3200000000000000000000), D2 := ((604076231874999832861 : Rat) / 3200000000000000000000), D3 := ((128701711874999837277 : Rat) / 3200000000000000000000), D4 := ((3900051874999995069 : Rat) / 100000000000000000000), LB := ((439059010072107 : Rat) / 200000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8789468231874999832861 : Rat) / 3200000000000000000000), R := ((879336828374999982793 : Rat) / 320000000000000000000), D0 := ((879336828374999982793 : Rat) / 320000000000000000000), D1 := ((297744796374999982793 : Rat) / 320000000000000000000), D2 := ((60797628374999982793 : Rat) / 320000000000000000000), D3 := ((66300881874999916173 : Rat) / 1600000000000000000000), D4 := ((120901608124999847139 : Rat) / 3200000000000000000000), LB := ((255100738991203 : Rat) / 80000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((879336828374999982793 : Rat) / 320000000000000000000), R := ((8797268335624999822999 : Rat) / 3200000000000000000000), D0 := ((8797268335624999822999 : Rat) / 3200000000000000000000), D1 := ((2981348015624999822999 : Rat) / 3200000000000000000000), D2 := ((611876335624999822999 : Rat) / 3200000000000000000000), D3 := ((27300363124999965483 : Rat) / 640000000000000000000), D4 := ((11700155624999985207 : Rat) / 320000000000000000000), LB := ((278082593013769 : Rat) / 62500000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8797268335624999822999 : Rat) / 3200000000000000000000), R := ((2200292096874999954517 : Rat) / 800000000000000000000), D0 := ((2200292096874999954517 : Rat) / 800000000000000000000), D1 := ((746312016874999954517 : Rat) / 800000000000000000000), D2 := ((153944096874999954517 : Rat) / 800000000000000000000), D3 := ((35100466874999955621 : Rat) / 800000000000000000000), D4 := ((113101504374999857001 : Rat) / 3200000000000000000000), LB := ((1197523035706971 : Rat) / 200000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2200292096874999954517 : Rat) / 800000000000000000000), R := ((4404484245624999904103 : Rat) / 1600000000000000000000), D0 := ((4404484245624999904103 : Rat) / 1600000000000000000000), D1 := ((1496524085624999904103 : Rat) / 1600000000000000000000), D2 := ((311788245624999904103 : Rat) / 1600000000000000000000), D3 := ((74100985624999906311 : Rat) / 1600000000000000000000), D4 := ((27300363124999965483 : Rat) / 800000000000000000000), LB := ((5563816977654179 : Rat) / 2000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4404484245624999904103 : Rat) / 1600000000000000000000), R := ((1102096074374999974793 : Rat) / 400000000000000000000), D0 := ((1102096074374999974793 : Rat) / 400000000000000000000), D1 := ((375106034374999974793 : Rat) / 400000000000000000000), D2 := ((78922074374999974793 : Rat) / 400000000000000000000), D3 := ((3900051874999995069 : Rat) / 80000000000000000000), D4 := ((50700674374999935897 : Rat) / 1600000000000000000000), LB := ((14933067845973147 : Rat) / 2000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1102096074374999974793 : Rat) / 400000000000000000000), R := ((441618440124999988931 : Rat) / 160000000000000000000), D0 := ((441618440124999988931 : Rat) / 160000000000000000000), D1 := ((150822424124999988931 : Rat) / 160000000000000000000), D2 := ((32348840124999988931 : Rat) / 160000000000000000000), D3 := ((42900570624999945759 : Rat) / 800000000000000000000), D4 := ((11700155624999985207 : Rat) / 400000000000000000000), LB := ((3934910219835941 : Rat) / 1000000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((441618440124999988931 : Rat) / 160000000000000000000), R := ((552998063124999984931 : Rat) / 200000000000000000000), D0 := ((552998063124999984931 : Rat) / 200000000000000000000), D1 := ((189503043124999984931 : Rat) / 200000000000000000000), D2 := ((41411063124999984931 : Rat) / 200000000000000000000), D3 := ((11700155624999985207 : Rat) / 200000000000000000000), D4 := ((3900051874999995069 : Rat) / 160000000000000000000), LB := ((132351857302717 : Rat) / 6250000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((552998063124999984931 : Rat) / 200000000000000000000), R := ((1109896178124999964931 : Rat) / 400000000000000000000), D0 := ((1109896178124999964931 : Rat) / 400000000000000000000), D1 := ((382906138124999964931 : Rat) / 400000000000000000000), D2 := ((86722178124999964931 : Rat) / 400000000000000000000), D3 := ((27300363124999965483 : Rat) / 400000000000000000000), D4 := ((3900051874999995069 : Rat) / 200000000000000000000), LB := ((585724248435453 : Rat) / 20000000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1109896178124999964931 : Rat) / 400000000000000000000), R := ((27844905749999999 : Rat) / 10000000000000000), D0 := ((27844905749999999 : Rat) / 10000000000000000), D1 := ((9670154749999999 : Rat) / 10000000000000000), D2 := ((2265555749999999 : Rat) / 10000000000000000), D3 := ((3900051874999995069 : Rat) / 50000000000000000000), D4 := ((3900051874999995069 : Rat) / 400000000000000000000), LB := ((411102271914807 : Rat) / 3125000000000000) },
  { w1 := ((1074749137863177 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((167667847221913 : Rat) / 2500000000000000), w4 := ((3941347948802067 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135324476874999999931 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27844905749999999 : Rat) / 10000000000000000), R := ((27989033482142857151 : Rat) / 10000000000000000000), D0 := ((27989033482142857151 : Rat) / 10000000000000000000), D1 := ((9814282482142857151 : Rat) / 10000000000000000000), D2 := ((2409683482142857151 : Rat) / 10000000000000000000), D3 := ((18049572405133929 : Rat) / 195312500000000000), D4 := ((144127732142858151 : Rat) / 10000000000000000000), LB := ((6277879275892517 : Rat) / 1000000000000000000) }
]

def block095RightChunk000L : Rat := ((2810481026785714287 : Rat) / 1562500000000000000)
def block095RightChunk000R : Rat := ((27989033482142857151 : Rat) / 10000000000000000000)

def block095RightChunk000Certificate : Bool :=
  allBoxesValid block095RightChunk000 &&
  coversFromBool block095RightChunk000 block095RightChunk000L block095RightChunk000R

theorem block095RightChunk000Certificate_eq_true :
    block095RightChunk000Certificate = true := by
  native_decide

def block095RightChainCertificate : Bool :=
  decide (
    block095RightL = ((2810481026785714287 : Rat) / 1562500000000000000) /\
    ((27989033482142857151 : Rat) / 10000000000000000000) = block095RightR)

theorem block095RightChainCertificate_eq_true :
    block095RightChainCertificate = true := by
  native_decide

def block095LeftBoxCount : Nat := boxCount block095LeftBoxes
def block095RightBoxCount : Nat := 64

def block095_rational_certificate : Prop :=
    block095LeftCertificate = true /\
    block095RightChainCertificate = true /\
    block095RightChunk000Certificate = true

theorem block095_rational_certificate_proof :
    block095_rational_certificate := by
  exact ⟨block095LeftCertificate_eq_true, block095RightChainCertificate_eq_true, block095RightChunk000Certificate_eq_true⟩

end Block095
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block095

open Set

def block095W1 : Rat := ((1074749137863177 : Rat) / 500000000000000)
def block095W2 : Rat := (0 : Rat)
def block095W3 : Rat := ((167667847221913 : Rat) / 2500000000000000)
def block095W4 : Rat := ((3941347948802067 : Rat) / 20000000000000000)
def block095S1 : Rat := ((18174751 : Rat) / 10000000)
def block095S2 : Rat := ((511587 : Rat) / 200000)
def block095S3 : Rat := ((135324476874999999931 : Rat) / 50000000000000000000)
def block095S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block095V (y : ℝ) : ℝ :=
  ratPotential block095W1 block095W2 block095W3 block095W4 block095S1 block095S2 block095S3 block095S4 y

def block095LeftParamsCertificate : Bool :=
  allBoxesSameParams block095LeftBoxes block095W1 block095W2 block095W3 block095W4 block095S1 block095S2 block095S3 block095S4

theorem block095LeftParamsCertificate_eq_true :
    block095LeftParamsCertificate = true := by
  native_decide

theorem block095_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block095LeftL : ℝ) (block095LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block095S1 : ℝ))
    (hy2ne : y ≠ (block095S2 : ℝ))
    (hy3ne : y ≠ (block095S3 : ℝ))
    (hy4ne : y ≠ (block095S4 : ℝ)) :
    0 < block095V y := by
  have hcert := block095LeftCertificate_eq_true
  unfold block095LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block095LeftBoxes) (lo := block095LeftL) (hi := block095LeftR)
    (w1 := block095W1) (w2 := block095W2) (w3 := block095W3) (w4 := block095W4)
    (s1 := block095S1) (s2 := block095S2) (s3 := block095S3) (s4 := block095S4)
    hboxes hcover block095LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block095RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block095RightChunk000 block095W1 block095W2 block095W3 block095W4 block095S1 block095S2 block095S3 block095S4

theorem block095RightChunk000ParamsCertificate_eq_true :
    block095RightChunk000ParamsCertificate = true := by
  native_decide

theorem block095_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block095RightChunk000L : ℝ) (block095RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block095S1 : ℝ))
    (hy2ne : y ≠ (block095S2 : ℝ))
    (hy3ne : y ≠ (block095S3 : ℝ))
    (hy4ne : y ≠ (block095S4 : ℝ)) :
    0 < block095V y := by
  have hcert := block095RightChunk000Certificate_eq_true
  unfold block095RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block095RightChunk000) (lo := block095RightChunk000L) (hi := block095RightChunk000R)
    (w1 := block095W1) (w2 := block095W2) (w3 := block095W3) (w4 := block095W4)
    (s1 := block095S1) (s2 := block095S2) (s3 := block095S3) (s4 := block095S4)
    hboxes hcover block095RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block095_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block095RightL : ℝ) (block095RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block095S1 : ℝ))
    (hy2ne : y ≠ (block095S2 : ℝ))
    (hy3ne : y ≠ (block095S3 : ℝ))
    (hy4ne : y ≠ (block095S4 : ℝ)) :
    0 < block095V y := by
  have hL : (block095RightChunk000L : ℝ) = (block095RightL : ℝ) := by
    norm_num [block095RightChunk000L, block095RightL]
  have hR : (block095RightChunk000R : ℝ) = (block095RightR : ℝ) := by
    norm_num [block095RightChunk000R, block095RightR]
  have hyc : y ∈ Icc (block095RightChunk000L : ℝ) (block095RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block095_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block095_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block095LeftL : ℝ) (block095LeftR : ℝ) →
    y ≠ 0 → y ≠ (block095S1 : ℝ) → y ≠ (block095S2 : ℝ) →
    y ≠ (block095S3 : ℝ) → y ≠ (block095S4 : ℝ) → 0 < block095V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block095RightL : ℝ) (block095RightR : ℝ) →
    y ≠ 0 → y ≠ (block095S1 : ℝ) → y ≠ (block095S2 : ℝ) →
    y ≠ (block095S3 : ℝ) → y ≠ (block095S4 : ℝ) → 0 < block095V y)

theorem block095_reallog_certificate_proof :
    block095_reallog_certificate := by
  exact ⟨block095_left_V_pos, block095_right_V_pos⟩

end Block095
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block095.block095V
#check Erdos1038Lean.M1817475.Block095.block095_left_V_pos
#check Erdos1038Lean.M1817475.Block095.block095_right_V_pos
#check Erdos1038Lean.M1817475.Block095.block095_reallog_certificate_proof
