/-
Self-contained Lean4Web paste file.
Block 377 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block377

def block377LeftL : Rat := ((18589484375000000081 : Rat) / 25000000000000000000)
def block377LeftR : Rat := ((37188743303571428733 : Rat) / 50000000000000000000)
def block377RightL : Rat := ((43589484375000000081 : Rat) / 25000000000000000000)
def block377RightR : Rat := ((137188743303571428733 : Rat) / 50000000000000000000)

def block377LeftBoxes : List RatBox := [
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18589484375000000081 : Rat) / 25000000000000000000), R := ((37188743303571428733 : Rat) / 50000000000000000000), D0 := ((37188743303571428733 : Rat) / 50000000000000000000), D1 := ((26847393124999999919 : Rat) / 25000000000000000000), D2 := ((45358890624999999919 : Rat) / 25000000000000000000), D3 := ((95584575089285714167 : Rat) / 50000000000000000000), D4 := ((25359884419642855859 : Rat) / 12500000000000000000), LB := ((1243645413634839 : Rat) / 200000000000000000) }
]

def block377LeftCertificate : Bool :=
  allBoxesValid block377LeftBoxes &&
  coversFromBool block377LeftBoxes block377LeftL block377LeftR

theorem block377LeftCertificate_eq_true :
    block377LeftCertificate = true := by
  native_decide

def block377RightChunk000 : List RatBox := [
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43589484375000000081 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1847393124999999919 : Rat) / 25000000000000000000), D2 := ((20358890624999999919 : Rat) / 25000000000000000000), D3 := ((45584575089285714167 : Rat) / 50000000000000000000), D4 := ((12859884419642855859 : Rat) / 12500000000000000000), LB := ((1650378441035629 : Rat) / 1000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41889788839285714329 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((11514272215076607 : Rat) / 100000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23378291339285714329 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((1513826468165737 : Rat) / 20000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18750416964285714329 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((4635915340684431 : Rat) / 100000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16436479776785714329 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((415091223365221 : Rat) / 10000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((15279511183035714329 : Rat) / 50000000000000000000), D4 := ((10567236886160711799 : Rat) / 25000000000000000000), LB := ((19177894440790613 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14122542589285714329 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((16595137055258613 : Rat) / 50000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12965573995535714329 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((13223584129124999 : Rat) / 2000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12387089698660714329 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((22236562811592253 : Rat) / 100000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11808605401785714329 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((13553816453203 : Rat) / 2500000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11519363253348214329 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((1566040554110179 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11230121104910714329 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((11506747706147569 : Rat) / 10000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10940878956473214329 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((4643716167734763 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10796257882254464329 : Rat) / 50000000000000000000), D4 := ((8325610235770086799 : Rat) / 25000000000000000000), LB := ((489880140592279 : Rat) / 125000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10651636808035714329 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((3280640563460141 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10507015733816964329 : Rat) / 50000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((1365352721897889 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10362394659598214329 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((141973474934479 : Rat) / 62500000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10217773585379464329 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((3811506716388413 : Rat) / 2000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10073152511160714329 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((408979727042999 : Rat) / 250000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9928531436941964329 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((2929895350170797 : Rat) / 2000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9783910362723214329 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((13959300661090523 : Rat) / 10000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9639289288504464329 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((7160969889335733 : Rat) / 5000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9494668214285714329 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((15773305660986003 : Rat) / 10000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9350047140066964329 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((18352238786996933 : Rat) / 10000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9205426065848214329 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((276260636319043 : Rat) / 125000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9060804991629464329 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((2706492251450393 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8916183917410714329 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((1664718339786167 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((8771562843191964329 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((4084377418139329 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8626941768973214329 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((12047384512095527 : Rat) / 100000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8337699620535714329 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((2381728229423119 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8048457472098214329 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((5283361869731523 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7759215323660714329 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((1780524979691639 : Rat) / 200000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7469973175223214329 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((6669089584229723 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7180731026785714329 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((9386278666502351 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6602246729910714329 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((2986490252833783 : Rat) / 125000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6023762433035714329 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((13823408597175027 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516453793839285714329 : Rat) / 200000000000000000000), D0 := ((516453793839285714329 : Rat) / 200000000000000000000), D1 := ((152958773839285714329 : Rat) / 200000000000000000000), D2 := ((4866793839285714329 : Rat) / 200000000000000000000), D3 := ((4866793839285714329 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((9022809005000229 : Rat) / 250000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516453793839285714329 : Rat) / 200000000000000000000), R := ((260660293839285714329 : Rat) / 100000000000000000000), D0 := ((260660293839285714329 : Rat) / 100000000000000000000), D1 := ((78912783839285714329 : Rat) / 100000000000000000000), D2 := ((4866793839285714329 : Rat) / 100000000000000000000), D3 := ((14600381517857142987 : Rat) / 200000000000000000000), D4 := ((38020231874999980063 : Rat) / 200000000000000000000), LB := ((2974595356098539 : Rat) / 100000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((260660293839285714329 : Rat) / 100000000000000000000), R := ((132763543839285714329 : Rat) / 50000000000000000000), D0 := ((132763543839285714329 : Rat) / 50000000000000000000), D1 := ((41889788839285714329 : Rat) / 50000000000000000000), D2 := ((4866793839285714329 : Rat) / 50000000000000000000), D3 := ((4866793839285714329 : Rat) / 100000000000000000000), D4 := ((16576719017857132867 : Rat) / 100000000000000000000), LB := ((10733477350778897 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((132763543839285714329 : Rat) / 50000000000000000000), R := ((13386984370535714293 : Rat) / 5000000000000000000), D0 := ((13386984370535714293 : Rat) / 5000000000000000000), D1 := ((4299608870535714293 : Rat) / 5000000000000000000), D2 := ((597309370535714293 : Rat) / 5000000000000000000), D3 := ((1106299866071428601 : Rat) / 50000000000000000000), D4 := ((5854962589285709269 : Rat) / 50000000000000000000), LB := ((14329999584484787 : Rat) / 100000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((13386984370535714293 : Rat) / 5000000000000000000), R := ((134976143571428571531 : Rat) / 50000000000000000000), D0 := ((134976143571428571531 : Rat) / 50000000000000000000), D1 := ((44102388571428571531 : Rat) / 50000000000000000000), D2 := ((7079393571428571531 : Rat) / 50000000000000000000), D3 := ((1106299866071428601 : Rat) / 25000000000000000000), D4 := ((1187165680803570167 : Rat) / 12500000000000000000), LB := ((12862264757086267 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((134976143571428571531 : Rat) / 50000000000000000000), R := ((271058587008928571663 : Rat) / 100000000000000000000), D0 := ((271058587008928571663 : Rat) / 100000000000000000000), D1 := ((89311077008928571663 : Rat) / 100000000000000000000), D2 := ((15265087008928571663 : Rat) / 100000000000000000000), D3 := ((1106299866071428601 : Rat) / 20000000000000000000), D4 := ((3642362857142852067 : Rat) / 50000000000000000000), LB := ((4763624163543173 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((271058587008928571663 : Rat) / 100000000000000000000), R := ((543223473883928571927 : Rat) / 200000000000000000000), D0 := ((543223473883928571927 : Rat) / 200000000000000000000), D1 := ((179728453883928571927 : Rat) / 200000000000000000000), D2 := ((31636473883928571927 : Rat) / 200000000000000000000), D3 := ((12169298526785714611 : Rat) / 200000000000000000000), D4 := ((6178425848214275533 : Rat) / 100000000000000000000), LB := ((1079313238314783 : Rat) / 125000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((543223473883928571927 : Rat) / 200000000000000000000), R := ((217510649526785714491 : Rat) / 80000000000000000000), D0 := ((217510649526785714491 : Rat) / 80000000000000000000), D1 := ((72112641526785714491 : Rat) / 80000000000000000000), D2 := ((12875849526785714491 : Rat) / 80000000000000000000), D3 := ((25444896919642857823 : Rat) / 400000000000000000000), D4 := ((2250110366071424493 : Rat) / 40000000000000000000), LB := ((5164846573201237 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((217510649526785714491 : Rat) / 80000000000000000000), R := ((34020610859375000033 : Rat) / 12500000000000000000), D0 := ((34020610859375000033 : Rat) / 12500000000000000000), D1 := ((11302172109375000033 : Rat) / 12500000000000000000), D2 := ((2046423359375000033 : Rat) / 12500000000000000000), D3 := ((3318899598214285803 : Rat) / 50000000000000000000), D4 := ((21394803794642816329 : Rat) / 400000000000000000000), LB := ((6267646923457271 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((34020610859375000033 : Rat) / 12500000000000000000), R := ((1089765847366071429657 : Rat) / 400000000000000000000), D0 := ((1089765847366071429657 : Rat) / 400000000000000000000), D1 := ((362775807366071429657 : Rat) / 400000000000000000000), D2 := ((66591847366071429657 : Rat) / 400000000000000000000), D3 := ((1106299866071428601 : Rat) / 16000000000000000000), D4 := ((1268031495535711733 : Rat) / 25000000000000000000), LB := ((28764347574637417 : Rat) / 10000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1089765847366071429657 : Rat) / 400000000000000000000), R := ((545436073616071429129 : Rat) / 200000000000000000000), D0 := ((545436073616071429129 : Rat) / 200000000000000000000), D1 := ((181941053616071429129 : Rat) / 200000000000000000000), D2 := ((33849073616071429129 : Rat) / 200000000000000000000), D3 := ((14381898258928571813 : Rat) / 200000000000000000000), D4 := ((19182204062499959127 : Rat) / 400000000000000000000), LB := ((176208562962743 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545436073616071429129 : Rat) / 200000000000000000000), R := ((2182850594330357145117 : Rat) / 800000000000000000000), D0 := ((2182850594330357145117 : Rat) / 800000000000000000000), D1 := ((728870514330357145117 : Rat) / 800000000000000000000), D2 := ((136502594330357145117 : Rat) / 800000000000000000000), D3 := ((58633892901785715853 : Rat) / 800000000000000000000), D4 := ((9037952098214265263 : Rat) / 200000000000000000000), LB := ((1658797757951691 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2182850594330357145117 : Rat) / 800000000000000000000), R := ((1091978447098214286859 : Rat) / 400000000000000000000), D0 := ((1091978447098214286859 : Rat) / 400000000000000000000), D1 := ((364988407098214286859 : Rat) / 400000000000000000000), D2 := ((68804447098214286859 : Rat) / 400000000000000000000), D3 := ((29870096383928572227 : Rat) / 400000000000000000000), D4 := ((35045508526785632451 : Rat) / 800000000000000000000), LB := ((25517473431089233 : Rat) / 10000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1091978447098214286859 : Rat) / 400000000000000000000), R := ((2185063194062500002319 : Rat) / 800000000000000000000), D0 := ((2185063194062500002319 : Rat) / 800000000000000000000), D1 := ((731083114062500002319 : Rat) / 800000000000000000000), D2 := ((138715194062500002319 : Rat) / 800000000000000000000), D3 := ((12169298526785714611 : Rat) / 160000000000000000000), D4 := ((678784173214284077 : Rat) / 16000000000000000000), LB := ((496196428563439 : Rat) / 250000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2185063194062500002319 : Rat) / 800000000000000000000), R := ((54654237348214285773 : Rat) / 20000000000000000000), D0 := ((54654237348214285773 : Rat) / 20000000000000000000), D1 := ((18304735348214285773 : Rat) / 20000000000000000000), D2 := ((3495537348214285773 : Rat) / 20000000000000000000), D3 := ((7744099062500000207 : Rat) / 100000000000000000000), D4 := ((32832908794642775249 : Rat) / 800000000000000000000), LB := ((10149827450881 : Rat) / 6250000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((54654237348214285773 : Rat) / 20000000000000000000), R := ((2187275793794642859521 : Rat) / 800000000000000000000), D0 := ((2187275793794642859521 : Rat) / 800000000000000000000), D1 := ((733295713794642859521 : Rat) / 800000000000000000000), D2 := ((140927793794642859521 : Rat) / 800000000000000000000), D3 := ((63059092366071430257 : Rat) / 800000000000000000000), D4 := ((3965826116071418331 : Rat) / 100000000000000000000), LB := ((738813023305751 : Rat) / 500000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2187275793794642859521 : Rat) / 800000000000000000000), R := ((1094191046830357144061 : Rat) / 400000000000000000000), D0 := ((1094191046830357144061 : Rat) / 400000000000000000000), D1 := ((367201006830357144061 : Rat) / 400000000000000000000), D2 := ((71017046830357144061 : Rat) / 400000000000000000000), D3 := ((32082696116071429429 : Rat) / 400000000000000000000), D4 := ((30620309062499918047 : Rat) / 800000000000000000000), LB := ((1944062887124301 : Rat) / 1250000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094191046830357144061 : Rat) / 400000000000000000000), R := ((2189488393526785716723 : Rat) / 800000000000000000000), D0 := ((2189488393526785716723 : Rat) / 800000000000000000000), D1 := ((735508313526785716723 : Rat) / 800000000000000000000), D2 := ((143140393526785716723 : Rat) / 800000000000000000000), D3 := ((65271692098214287459 : Rat) / 800000000000000000000), D4 := ((14757004598214244723 : Rat) / 400000000000000000000), LB := ((3735374697135141 : Rat) / 2000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2189488393526785716723 : Rat) / 800000000000000000000), R := ((547648673348214286331 : Rat) / 200000000000000000000), D0 := ((547648673348214286331 : Rat) / 200000000000000000000), D1 := ((184153653348214286331 : Rat) / 200000000000000000000), D2 := ((36061673348214286331 : Rat) / 200000000000000000000), D3 := ((3318899598214285803 : Rat) / 40000000000000000000), D4 := ((5681541866071412169 : Rat) / 160000000000000000000), LB := ((12136513030253093 : Rat) / 5000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((547648673348214286331 : Rat) / 200000000000000000000), R := ((87668039730357142957 : Rat) / 32000000000000000000), D0 := ((87668039730357142957 : Rat) / 32000000000000000000), D1 := ((29508836530357142957 : Rat) / 32000000000000000000), D2 := ((5814119730357142957 : Rat) / 32000000000000000000), D3 := ((67484291830357144661 : Rat) / 800000000000000000000), D4 := ((6825352366071408061 : Rat) / 200000000000000000000), LB := ((3248207955291349 : Rat) / 1000000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87668039730357142957 : Rat) / 32000000000000000000), R := ((1096403646562500001263 : Rat) / 400000000000000000000), D0 := ((1096403646562500001263 : Rat) / 400000000000000000000), D1 := ((369413606562500001263 : Rat) / 400000000000000000000), D2 := ((73229646562500001263 : Rat) / 400000000000000000000), D3 := ((34295295848214286631 : Rat) / 400000000000000000000), D4 := ((26195109598214203643 : Rat) / 800000000000000000000), LB := ((543316579611007 : Rat) / 125000000000000000) },
  { w1 := ((8551245605469473 : Rat) / 10000000000000000), w2 := ((1165530831939389 : Rat) / 25000000000000000), w3 := ((7865769051127887 : Rat) / 50000000000000000), w4 := ((2802276557638767 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132763543839285714329 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1096403646562500001263 : Rat) / 400000000000000000000), R := ((137188743303571428733 : Rat) / 50000000000000000000), D0 := ((137188743303571428733 : Rat) / 50000000000000000000), D1 := ((46314988303571428733 : Rat) / 50000000000000000000), D2 := ((9291993303571428733 : Rat) / 50000000000000000000), D3 := ((1106299866071428601 : Rat) / 12500000000000000000), D4 := ((12544404866071387521 : Rat) / 400000000000000000000), LB := ((5666884330514377 : Rat) / 5000000000000000000) }
]

def block377RightChunk000L : Rat := ((43589484375000000081 : Rat) / 25000000000000000000)
def block377RightChunk000R : Rat := ((137188743303571428733 : Rat) / 50000000000000000000)

def block377RightChunk000Certificate : Bool :=
  allBoxesValid block377RightChunk000 &&
  coversFromBool block377RightChunk000 block377RightChunk000L block377RightChunk000R

theorem block377RightChunk000Certificate_eq_true :
    block377RightChunk000Certificate = true := by
  native_decide

def block377RightChainCertificate : Bool :=
  decide (
    block377RightL = ((43589484375000000081 : Rat) / 25000000000000000000) /\
    ((137188743303571428733 : Rat) / 50000000000000000000) = block377RightR)

theorem block377RightChainCertificate_eq_true :
    block377RightChainCertificate = true := by
  native_decide

def block377LeftBoxCount : Nat := boxCount block377LeftBoxes
def block377RightBoxCount : Nat := 58

def block377_rational_certificate : Prop :=
    block377LeftCertificate = true /\
    block377RightChainCertificate = true /\
    block377RightChunk000Certificate = true

theorem block377_rational_certificate_proof :
    block377_rational_certificate := by
  exact ⟨block377LeftCertificate_eq_true, block377RightChainCertificate_eq_true, block377RightChunk000Certificate_eq_true⟩

end Block377
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block377

open Set

def block377W1 : Rat := ((8551245605469473 : Rat) / 10000000000000000)
def block377W2 : Rat := ((1165530831939389 : Rat) / 25000000000000000)
def block377W3 : Rat := ((7865769051127887 : Rat) / 50000000000000000)
def block377W4 : Rat := ((2802276557638767 : Rat) / 20000000000000000)
def block377S1 : Rat := ((18174751 : Rat) / 10000000)
def block377S2 : Rat := ((511587 : Rat) / 200000)
def block377S3 : Rat := ((132763543839285714329 : Rat) / 50000000000000000000)
def block377S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block377V (y : ℝ) : ℝ :=
  ratPotential block377W1 block377W2 block377W3 block377W4 block377S1 block377S2 block377S3 block377S4 y

def block377LeftParamsCertificate : Bool :=
  allBoxesSameParams block377LeftBoxes block377W1 block377W2 block377W3 block377W4 block377S1 block377S2 block377S3 block377S4

theorem block377LeftParamsCertificate_eq_true :
    block377LeftParamsCertificate = true := by
  native_decide

theorem block377_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block377LeftL : ℝ) (block377LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block377S1 : ℝ))
    (hy2ne : y ≠ (block377S2 : ℝ))
    (hy3ne : y ≠ (block377S3 : ℝ))
    (hy4ne : y ≠ (block377S4 : ℝ)) :
    0 < block377V y := by
  have hcert := block377LeftCertificate_eq_true
  unfold block377LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block377LeftBoxes) (lo := block377LeftL) (hi := block377LeftR)
    (w1 := block377W1) (w2 := block377W2) (w3 := block377W3) (w4 := block377W4)
    (s1 := block377S1) (s2 := block377S2) (s3 := block377S3) (s4 := block377S4)
    hboxes hcover block377LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block377RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block377RightChunk000 block377W1 block377W2 block377W3 block377W4 block377S1 block377S2 block377S3 block377S4

theorem block377RightChunk000ParamsCertificate_eq_true :
    block377RightChunk000ParamsCertificate = true := by
  native_decide

theorem block377_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block377RightChunk000L : ℝ) (block377RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block377S1 : ℝ))
    (hy2ne : y ≠ (block377S2 : ℝ))
    (hy3ne : y ≠ (block377S3 : ℝ))
    (hy4ne : y ≠ (block377S4 : ℝ)) :
    0 < block377V y := by
  have hcert := block377RightChunk000Certificate_eq_true
  unfold block377RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block377RightChunk000) (lo := block377RightChunk000L) (hi := block377RightChunk000R)
    (w1 := block377W1) (w2 := block377W2) (w3 := block377W3) (w4 := block377W4)
    (s1 := block377S1) (s2 := block377S2) (s3 := block377S3) (s4 := block377S4)
    hboxes hcover block377RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block377_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block377RightL : ℝ) (block377RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block377S1 : ℝ))
    (hy2ne : y ≠ (block377S2 : ℝ))
    (hy3ne : y ≠ (block377S3 : ℝ))
    (hy4ne : y ≠ (block377S4 : ℝ)) :
    0 < block377V y := by
  have hL : (block377RightChunk000L : ℝ) = (block377RightL : ℝ) := by
    norm_num [block377RightChunk000L, block377RightL]
  have hR : (block377RightChunk000R : ℝ) = (block377RightR : ℝ) := by
    norm_num [block377RightChunk000R, block377RightR]
  have hyc : y ∈ Icc (block377RightChunk000L : ℝ) (block377RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block377_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block377_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block377LeftL : ℝ) (block377LeftR : ℝ) →
    y ≠ 0 → y ≠ (block377S1 : ℝ) → y ≠ (block377S2 : ℝ) →
    y ≠ (block377S3 : ℝ) → y ≠ (block377S4 : ℝ) → 0 < block377V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block377RightL : ℝ) (block377RightR : ℝ) →
    y ≠ 0 → y ≠ (block377S1 : ℝ) → y ≠ (block377S2 : ℝ) →
    y ≠ (block377S3 : ℝ) → y ≠ (block377S4 : ℝ) → 0 < block377V y)

theorem block377_reallog_certificate_proof :
    block377_reallog_certificate := by
  exact ⟨block377_left_V_pos, block377_right_V_pos⟩

end Block377
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block377.block377V
#check Erdos1038Lean.M1817475.Block377.block377_left_V_pos
#check Erdos1038Lean.M1817475.Block377.block377_right_V_pos
#check Erdos1038Lean.M1817475.Block377.block377_reallog_certificate_proof
