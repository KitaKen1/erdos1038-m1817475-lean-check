/-
Self-contained Lean4Web paste file.
Block 395 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block395

def block395LeftL : Rat := ((9250756696428571471 : Rat) / 12500000000000000000)
def block395LeftR : Rat := ((7402560267857142891 : Rat) / 10000000000000000000)
def block395RightL : Rat := ((21750756696428571471 : Rat) / 12500000000000000000)
def block395RightR : Rat := ((27402560267857142891 : Rat) / 10000000000000000000)

def block395LeftBoxes : List RatBox := [
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((9250756696428571471 : Rat) / 12500000000000000000), R := ((7402560267857142891 : Rat) / 10000000000000000000), D0 := ((7402560267857142891 : Rat) / 10000000000000000000), D1 := ((13467682053571428529 : Rat) / 12500000000000000000), D2 := ((22723430803571428529 : Rat) / 12500000000000000000), D3 := ((95408633124999999889 : Rat) / 50000000000000000000), D4 := ((12763025915178570783 : Rat) / 6250000000000000000), LB := ((1807403945224939 : Rat) / 2000000000000000000) }
]

def block395LeftCertificate : Bool :=
  allBoxesValid block395LeftBoxes &&
  coversFromBool block395LeftBoxes block395LeftL block395LeftR

theorem block395LeftCertificate_eq_true :
    block395LeftCertificate = true := by
  native_decide

def block395RightChunk000 : List RatBox := [
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((21750756696428571471 : Rat) / 12500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((967682053571428529 : Rat) / 12500000000000000000), D2 := ((10223430803571428529 : Rat) / 12500000000000000000), D3 := ((45408633124999999889 : Rat) / 50000000000000000000), D4 := ((6513025915178570783 : Rat) / 6250000000000000000), LB := ((7332271588805933 : Rat) / 5000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41537904910714285773 : Rat) / 50000000000000000000), D4 := ((12058369776785713037 : Rat) / 12500000000000000000), LB := ((30433074798946483 : Rat) / 500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23026407410714285773 : Rat) / 50000000000000000000), D4 := ((7430495401785713037 : Rat) / 12500000000000000000), LB := ((8379948275548199 : Rat) / 200000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18398533035714285773 : Rat) / 50000000000000000000), D4 := ((6273526808035713037 : Rat) / 12500000000000000000), LB := ((2600732468011669 : Rat) / 125000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16084595848214285773 : Rat) / 50000000000000000000), D4 := ((5695042511160713037 : Rat) / 12500000000000000000), LB := ((2014123154297727 : Rat) / 100000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((14927627254464285773 : Rat) / 50000000000000000000), D4 := ((5405800362723213037 : Rat) / 12500000000000000000), LB := ((2230607532468537 : Rat) / 2000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13770658660714285773 : Rat) / 50000000000000000000), D4 := ((5116558214285713037 : Rat) / 12500000000000000000), LB := ((6526616975380123 : Rat) / 1000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((305201883 : Rat) / 128000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((13192174363839285773 : Rat) / 50000000000000000000), D4 := ((4971937140066963037 : Rat) / 12500000000000000000), LB := ((2553444807758487 : Rat) / 250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((12902932215401785773 : Rat) / 50000000000000000000), D4 := ((4899626602957588037 : Rat) / 12500000000000000000), LB := ((1777680880450841 : Rat) / 250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((766707007 : Rat) / 320000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12613690066964285773 : Rat) / 50000000000000000000), D4 := ((4827316065848213037 : Rat) / 12500000000000000000), LB := ((4260406075988599 : Rat) / 1000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((12324447918526785773 : Rat) / 50000000000000000000), D4 := ((4755005528738838037 : Rat) / 12500000000000000000), LB := ((417431832975039 : Rat) / 250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12035205770089285773 : Rat) / 50000000000000000000), D4 := ((4682694991629463037 : Rat) / 12500000000000000000), LB := ((221762661894033 : Rat) / 50000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((11890584695870535773 : Rat) / 50000000000000000000), D4 := ((4646539723074775537 : Rat) / 12500000000000000000), LB := ((16780872497178523 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((123561673 : Rat) / 51200000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11745963621651785773 : Rat) / 50000000000000000000), D4 := ((4610384454520088037 : Rat) / 12500000000000000000), LB := ((23473863092370317 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((11601342547433035773 : Rat) / 50000000000000000000), D4 := ((4574229185965400537 : Rat) / 12500000000000000000), LB := ((14101070216340217 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((387055803 : Rat) / 160000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11456721473214285773 : Rat) / 50000000000000000000), D4 := ((4538073917410713037 : Rat) / 12500000000000000000), LB := ((5456237820185283 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((12407999493 : Rat) / 5120000000), D0 := ((12407999493 : Rat) / 5120000000), D1 := ((3102526981 : Rat) / 5120000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((11312100398995535773 : Rat) / 50000000000000000000), D4 := ((4501918648856025537 : Rat) / 12500000000000000000), LB := ((11286460584962743 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12407999493 : Rat) / 5120000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((688627707 : Rat) / 5120000000), D3 := ((11239789861886160773 : Rat) / 50000000000000000000), D4 := ((4483841014578681787 : Rat) / 12500000000000000000), LB := ((942748444387187 : Rat) / 500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11167479324776785773 : Rat) / 50000000000000000000), D4 := ((4465763380301338037 : Rat) / 12500000000000000000), LB := ((1532808691228571 : Rat) / 1000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((11095168787667410773 : Rat) / 50000000000000000000), D4 := ((4447685746023994287 : Rat) / 12500000000000000000), LB := ((5997101812810629 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((11022858250558035773 : Rat) / 50000000000000000000), D4 := ((4429608111746650537 : Rat) / 12500000000000000000), LB := ((8855303528701453 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((10950547713448660773 : Rat) / 50000000000000000000), D4 := ((4411530477469306787 : Rat) / 12500000000000000000), LB := ((591342926511057 : Rat) / 1000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((81450589 : Rat) / 640000000), D3 := ((10878237176339285773 : Rat) / 50000000000000000000), D4 := ((4393452843191963037 : Rat) / 12500000000000000000), LB := ((31706837474546057 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((10805926639229910773 : Rat) / 50000000000000000000), D4 := ((4375375208914619287 : Rat) / 12500000000000000000), LB := ((3146161965293659 : Rat) / 50000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((24927067971 : Rat) / 10240000000), D0 := ((24927067971 : Rat) / 10240000000), D1 := ((6316122947 : Rat) / 10240000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10733616102120535773 : Rat) / 50000000000000000000), D4 := ((4357297574637275537 : Rat) / 12500000000000000000), LB := ((10626576991642767 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24927067971 : Rat) / 10240000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((1266186429 : Rat) / 10240000000), D3 := ((10697460833565848273 : Rat) / 50000000000000000000), D4 := ((2174129378749301831 : Rat) / 6250000000000000000), LB := ((2380702190458439 : Rat) / 2500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((24941877169 : Rat) / 10240000000), D0 := ((24941877169 : Rat) / 10240000000), D1 := ((1266186429 : Rat) / 2048000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((10661305565011160773 : Rat) / 50000000000000000000), D4 := ((4339219940359931787 : Rat) / 12500000000000000000), LB := ((8470814790653147 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24941877169 : Rat) / 10240000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((1251377231 : Rat) / 10240000000), D3 := ((10625150296456473273 : Rat) / 50000000000000000000), D4 := ((541272640402657489 : Rat) / 1562500000000000000), LB := ((7470893137301871 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((24956686367 : Rat) / 10240000000), D0 := ((24956686367 : Rat) / 10240000000), D1 := ((6345741343 : Rat) / 10240000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10588995027901785773 : Rat) / 50000000000000000000), D4 := ((4321142306082588037 : Rat) / 12500000000000000000), LB := ((6523346403338737 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24956686367 : Rat) / 10240000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((1236568033 : Rat) / 10240000000), D3 := ((10552839759347098273 : Rat) / 50000000000000000000), D4 := ((2156051744471958081 : Rat) / 6250000000000000000), LB := ((5628481822038123 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((4994299113 : Rat) / 2048000000), D0 := ((4994299113 : Rat) / 2048000000), D1 := ((6360550541 : Rat) / 10240000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((10516684490792410773 : Rat) / 50000000000000000000), D4 := ((4303064671805244287 : Rat) / 12500000000000000000), LB := ((23933056750732873 : Rat) / 50000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4994299113 : Rat) / 2048000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((244351767 : Rat) / 2048000000), D3 := ((10480529222237723273 : Rat) / 50000000000000000000), D4 := ((1073506463666643103 : Rat) / 3125000000000000000), LB := ((3998051762207633 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((24986304763 : Rat) / 10240000000), D0 := ((24986304763 : Rat) / 10240000000), D1 := ((6375359739 : Rat) / 10240000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10444373953683035773 : Rat) / 50000000000000000000), D4 := ((4284987037527900537 : Rat) / 12500000000000000000), LB := ((3263124747464319 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24986304763 : Rat) / 10240000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((1206949637 : Rat) / 10240000000), D3 := ((10408218685128348273 : Rat) / 50000000000000000000), D4 := ((2137974110194614331 : Rat) / 6250000000000000000), LB := ((5164314018809013 : Rat) / 20000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((25001113961 : Rat) / 10240000000), D0 := ((25001113961 : Rat) / 10240000000), D1 := ((6390168937 : Rat) / 10240000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((10372063416573660773 : Rat) / 50000000000000000000), D4 := ((4266909403250556787 : Rat) / 12500000000000000000), LB := ((9777401840847799 : Rat) / 50000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25001113961 : Rat) / 10240000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((1192140439 : Rat) / 10240000000), D3 := ((10335908148018973273 : Rat) / 50000000000000000000), D4 := ((266116911631992807 : Rat) / 781250000000000000), LB := ((2766863731537561 : Rat) / 20000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((156303241 : Rat) / 64000000), R := ((25015923159 : Rat) / 10240000000), D0 := ((25015923159 : Rat) / 10240000000), D1 := ((1280995627 : Rat) / 2048000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10299752879464285773 : Rat) / 50000000000000000000), D4 := ((4248831768973213037 : Rat) / 12500000000000000000), LB := ((8663538743280963 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25015923159 : Rat) / 10240000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((1177331241 : Rat) / 10240000000), D3 := ((10263597610909598273 : Rat) / 50000000000000000000), D4 := ((2119896475917270581 : Rat) / 6250000000000000000), LB := ((4045942073763187 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((10010812023 : Rat) / 4096000000), D0 := ((10010812023 : Rat) / 4096000000), D1 := ((12832170067 : Rat) / 20480000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((10227442342354910773 : Rat) / 50000000000000000000), D4 := ((4230754134695869287 : Rat) / 12500000000000000000), LB := ((3044368735640457 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10010812023 : Rat) / 4096000000), R := ((25030732357 : Rat) / 10240000000), D0 := ((25030732357 : Rat) / 10240000000), D1 := ((6419787333 : Rat) / 10240000000), D2 := ((466489737 : Rat) / 4096000000), D3 := ((10209364708077567023 : Rat) / 50000000000000000000), D4 := ((8452469452253066699 : Rat) / 25000000000000000000), LB := ((5903805157097541 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25030732357 : Rat) / 10240000000), R := ((50068869313 : Rat) / 20480000000), D0 := ((50068869313 : Rat) / 20480000000), D1 := ((2569395853 : Rat) / 4096000000), D2 := ((1162522043 : Rat) / 10240000000), D3 := ((10191287073800223273 : Rat) / 50000000000000000000), D4 := ((1055428829389299353 : Rat) / 3125000000000000000), LB := ((5732928985711927 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50068869313 : Rat) / 20480000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((2317639487 : Rat) / 20480000000), D3 := ((10173209439522879523 : Rat) / 50000000000000000000), D4 := ((8434391817975722949 : Rat) / 25000000000000000000), LB := ((697019342326341 : Rat) / 1250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((50083678511 : Rat) / 20480000000), D0 := ((50083678511 : Rat) / 20480000000), D1 := ((12861788463 : Rat) / 20480000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10155131805245535773 : Rat) / 50000000000000000000), D4 := ((4212676500418525537 : Rat) / 12500000000000000000), LB := ((2716764283630657 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50083678511 : Rat) / 20480000000), R := ((5009108311 : Rat) / 2048000000), D0 := ((5009108311 : Rat) / 2048000000), D1 := ((6434596531 : Rat) / 10240000000), D2 := ((2302830289 : Rat) / 20480000000), D3 := ((10137054170968192023 : Rat) / 50000000000000000000), D4 := ((8416314183698379199 : Rat) / 25000000000000000000), LB := ((1326274249268261 : Rat) / 2500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5009108311 : Rat) / 2048000000), R := ((50098487709 : Rat) / 20480000000), D0 := ((50098487709 : Rat) / 20480000000), D1 := ((12876597661 : Rat) / 20480000000), D2 := ((229542569 : Rat) / 2048000000), D3 := ((10118976536690848273 : Rat) / 50000000000000000000), D4 := ((2101818841639926831 : Rat) / 6250000000000000000), LB := ((2595453465732561 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50098487709 : Rat) / 20480000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((2288021091 : Rat) / 20480000000), D3 := ((10100898902413504523 : Rat) / 50000000000000000000), D4 := ((8398236549421035449 : Rat) / 25000000000000000000), LB := ((5091005655951941 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((50113296907 : Rat) / 20480000000), D0 := ((50113296907 : Rat) / 20480000000), D1 := ((12891406859 : Rat) / 20480000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((10082821268136160773 : Rat) / 50000000000000000000), D4 := ((4194598866141181787 : Rat) / 12500000000000000000), LB := ((5005440842312803 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50113296907 : Rat) / 20480000000), R := ((25060350753 : Rat) / 10240000000), D0 := ((25060350753 : Rat) / 10240000000), D1 := ((6449405729 : Rat) / 10240000000), D2 := ((2273211893 : Rat) / 20480000000), D3 := ((10064743633858817023 : Rat) / 50000000000000000000), D4 := ((8380158915143691699 : Rat) / 25000000000000000000), LB := ((4934260552832137 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25060350753 : Rat) / 10240000000), R := ((10025621221 : Rat) / 4096000000), D0 := ((10025621221 : Rat) / 4096000000), D1 := ((12906216057 : Rat) / 20480000000), D2 := ((1132903647 : Rat) / 10240000000), D3 := ((10046665999581473273 : Rat) / 50000000000000000000), D4 := ((523195006125313739 : Rat) / 1562500000000000000), LB := ((1951005297827213 : Rat) / 4000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10025621221 : Rat) / 4096000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 4096000000), D3 := ((10028588365304129523 : Rat) / 50000000000000000000), D4 := ((8362081280866347949 : Rat) / 25000000000000000000), LB := ((24176238868572897 : Rat) / 50000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((50142915303 : Rat) / 20480000000), D0 := ((50142915303 : Rat) / 20480000000), D1 := ((2584205051 : Rat) / 4096000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10010510731026785773 : Rat) / 50000000000000000000), D4 := ((4176521231863838037 : Rat) / 12500000000000000000), LB := ((961502680006443 : Rat) / 2000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50142915303 : Rat) / 20480000000), R := ((25075159951 : Rat) / 10240000000), D0 := ((25075159951 : Rat) / 10240000000), D1 := ((6464214927 : Rat) / 10240000000), D2 := ((2243593497 : Rat) / 20480000000), D3 := ((9992433096749442023 : Rat) / 50000000000000000000), D4 := ((8344003646589004199 : Rat) / 25000000000000000000), LB := ((479435979130749 : Rat) / 1000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25075159951 : Rat) / 10240000000), R := ((50157724501 : Rat) / 20480000000), D0 := ((50157724501 : Rat) / 20480000000), D1 := ((12935834453 : Rat) / 20480000000), D2 := ((1118094449 : Rat) / 10240000000), D3 := ((9974355462472098273 : Rat) / 50000000000000000000), D4 := ((2083741207362583081 : Rat) / 6250000000000000000), LB := ((47958370279452267 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50157724501 : Rat) / 20480000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((2228784299 : Rat) / 20480000000), D3 := ((9956277828194754523 : Rat) / 50000000000000000000), D4 := ((8325926012311660449 : Rat) / 25000000000000000000), LB := ((12029989018860071 : Rat) / 25000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((501651291 : Rat) / 204800000), R := ((50172533699 : Rat) / 20480000000), D0 := ((50172533699 : Rat) / 20480000000), D1 := ((12950643651 : Rat) / 20480000000), D2 := ((22213797 : Rat) / 204800000), D3 := ((9938200193917410773 : Rat) / 50000000000000000000), D4 := ((4158443597586494287 : Rat) / 12500000000000000000), LB := ((2421443224811387 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50172533699 : Rat) / 20480000000), R := ((25089969149 : Rat) / 10240000000), D0 := ((25089969149 : Rat) / 10240000000), D1 := ((51832193 : Rat) / 81920000), D2 := ((2213975101 : Rat) / 20480000000), D3 := ((9920122559640067023 : Rat) / 50000000000000000000), D4 := ((8307848378034316699 : Rat) / 25000000000000000000), LB := ((4888560900396799 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25089969149 : Rat) / 10240000000), R := ((50187342897 : Rat) / 20480000000), D0 := ((50187342897 : Rat) / 20480000000), D1 := ((12965452849 : Rat) / 20480000000), D2 := ((1103285251 : Rat) / 10240000000), D3 := ((9902044925362723273 : Rat) / 50000000000000000000), D4 := ((1037351195111955603 : Rat) / 3125000000000000000), LB := ((4949070737564343 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50187342897 : Rat) / 20480000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((2199165903 : Rat) / 20480000000), D3 := ((9883967291085379523 : Rat) / 50000000000000000000), D4 := ((8289770743756972949 : Rat) / 25000000000000000000), LB := ((628058521910807 : Rat) / 1250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((10040430419 : Rat) / 4096000000), D0 := ((10040430419 : Rat) / 4096000000), D1 := ((12980262047 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((9865889656808035773 : Rat) / 50000000000000000000), D4 := ((4140365963309150537 : Rat) / 12500000000000000000), LB := ((5114805869111949 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10040430419 : Rat) / 4096000000), R := ((25104778347 : Rat) / 10240000000), D0 := ((25104778347 : Rat) / 10240000000), D1 := ((6493833323 : Rat) / 10240000000), D2 := ((436871341 : Rat) / 4096000000), D3 := ((9847812022530692023 : Rat) / 50000000000000000000), D4 := ((8271693109479629199 : Rat) / 25000000000000000000), LB := ((5220136921104401 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25104778347 : Rat) / 10240000000), R := ((50216961293 : Rat) / 20480000000), D0 := ((50216961293 : Rat) / 20480000000), D1 := ((2599014249 : Rat) / 4096000000), D2 := ((1088476053 : Rat) / 10240000000), D3 := ((9829734388253348273 : Rat) / 50000000000000000000), D4 := ((2065663573085239331 : Rat) / 6250000000000000000), LB := ((2670257442469459 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50216961293 : Rat) / 20480000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((2169547507 : Rat) / 20480000000), D3 := ((9811656753976004523 : Rat) / 50000000000000000000), D4 := ((8253615475202285449 : Rat) / 25000000000000000000), LB := ((1095198754231641 : Rat) / 2000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((50231770491 : Rat) / 20480000000), D0 := ((50231770491 : Rat) / 20480000000), D1 := ((13009880443 : Rat) / 20480000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((9793579119698660773 : Rat) / 50000000000000000000), D4 := ((4122288329031806787 : Rat) / 12500000000000000000), LB := ((5626628052461669 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50231770491 : Rat) / 20480000000), R := ((5023917509 : Rat) / 2048000000), D0 := ((5023917509 : Rat) / 2048000000), D1 := ((6508642521 : Rat) / 10240000000), D2 := ((2154738309 : Rat) / 20480000000), D3 := ((9775501485421317023 : Rat) / 50000000000000000000), D4 := ((8235537840924941699 : Rat) / 25000000000000000000), LB := ((5792472669114979 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5023917509 : Rat) / 2048000000), R := ((50246579689 : Rat) / 20480000000), D0 := ((50246579689 : Rat) / 20480000000), D1 := ((13024689641 : Rat) / 20480000000), D2 := ((214733371 : Rat) / 2048000000), D3 := ((9757423851143973273 : Rat) / 50000000000000000000), D4 := ((64269523623330233 : Rat) / 195312500000000000), LB := ((119471660688647 : Rat) / 200000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50246579689 : Rat) / 20480000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((2139929111 : Rat) / 20480000000), D3 := ((9739346216866629523 : Rat) / 50000000000000000000), D4 := ((8217460206647597949 : Rat) / 25000000000000000000), LB := ((1542503760078237 : Rat) / 2500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((25134396743 : Rat) / 10240000000), D0 := ((25134396743 : Rat) / 10240000000), D1 := ((6523451719 : Rat) / 10240000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9721268582589285773 : Rat) / 50000000000000000000), D4 := ((4104210694754463037 : Rat) / 12500000000000000000), LB := ((9274745390627781 : Rat) / 250000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25134396743 : Rat) / 10240000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((1058857657 : Rat) / 10240000000), D3 := ((9685113314034598273 : Rat) / 50000000000000000000), D4 := ((2047585938807895581 : Rat) / 6250000000000000000), LB := ((8465520266531801 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((25149205941 : Rat) / 10240000000), D0 := ((25149205941 : Rat) / 10240000000), D1 := ((6538260917 : Rat) / 10240000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((9648958045479910773 : Rat) / 50000000000000000000), D4 := ((4086133060477119287 : Rat) / 12500000000000000000), LB := ((865189540597 : Rat) / 6250000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25149205941 : Rat) / 10240000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((1044048459 : Rat) / 10240000000), D3 := ((9612802776925223273 : Rat) / 50000000000000000000), D4 := ((1019273560834611853 : Rat) / 3125000000000000000), LB := ((496178152722751 : Rat) / 2500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((25164015139 : Rat) / 10240000000), D0 := ((25164015139 : Rat) / 10240000000), D1 := ((1310614023 : Rat) / 2048000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9576647508370535773 : Rat) / 50000000000000000000), D4 := ((4068055426199775537 : Rat) / 12500000000000000000), LB := ((2648257467819659 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25164015139 : Rat) / 10240000000), R := ((12585709869 : Rat) / 5120000000), D0 := ((12585709869 : Rat) / 5120000000), D1 := ((3280237357 : Rat) / 5120000000), D2 := ((1029239261 : Rat) / 10240000000), D3 := ((9540492239815848273 : Rat) / 50000000000000000000), D4 := ((2029508304530551831 : Rat) / 6250000000000000000), LB := ((6750847532550619 : Rat) / 20000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12585709869 : Rat) / 5120000000), R := ((25178824337 : Rat) / 10240000000), D0 := ((25178824337 : Rat) / 10240000000), D1 := ((6567879313 : Rat) / 10240000000), D2 := ((510917331 : Rat) / 5120000000), D3 := ((9504336971261160773 : Rat) / 50000000000000000000), D4 := ((4049977791922431787 : Rat) / 12500000000000000000), LB := ((2083353087483919 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25178824337 : Rat) / 10240000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((1014430063 : Rat) / 10240000000), D3 := ((9468181702706473273 : Rat) / 50000000000000000000), D4 := ((505117371847969989 : Rat) / 1562500000000000000), LB := ((1255652079725847 : Rat) / 2500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((5038726707 : Rat) / 2048000000), D0 := ((5038726707 : Rat) / 2048000000), D1 := ((6582688511 : Rat) / 10240000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9432026434151785773 : Rat) / 50000000000000000000), D4 := ((4031900157645088037 : Rat) / 12500000000000000000), LB := ((2971821502418953 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5038726707 : Rat) / 2048000000), R := ((12600519067 : Rat) / 5120000000), D0 := ((12600519067 : Rat) / 5120000000), D1 := ((659009311 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 2048000000), D3 := ((9395871165597098273 : Rat) / 50000000000000000000), D4 := ((2011430670253208081 : Rat) / 6250000000000000000), LB := ((1386066490897453 : Rat) / 2000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12600519067 : Rat) / 5120000000), R := ((25208442733 : Rat) / 10240000000), D0 := ((25208442733 : Rat) / 10240000000), D1 := ((6597497709 : Rat) / 10240000000), D2 := ((496108133 : Rat) / 5120000000), D3 := ((9359715897042410773 : Rat) / 50000000000000000000), D4 := ((4013822523367744287 : Rat) / 12500000000000000000), LB := ((399160427288589 : Rat) / 500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25208442733 : Rat) / 10240000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((984811667 : Rat) / 10240000000), D3 := ((9323560628487723273 : Rat) / 50000000000000000000), D4 := ((1001195926557268103 : Rat) / 3125000000000000000), LB := ((9102813062401571 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((25223251931 : Rat) / 10240000000), D0 := ((25223251931 : Rat) / 10240000000), D1 := ((6612306907 : Rat) / 10240000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9287405359933035773 : Rat) / 50000000000000000000), D4 := ((3995744889090400537 : Rat) / 12500000000000000000), LB := ((12862122440329 : Rat) / 12500000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25223251931 : Rat) / 10240000000), R := ((2523065653 : Rat) / 1024000000), D0 := ((2523065653 : Rat) / 1024000000), D1 := ((3309855753 : Rat) / 5120000000), D2 := ((970002469 : Rat) / 10240000000), D3 := ((9251250091378348273 : Rat) / 50000000000000000000), D4 := ((1993353035975864331 : Rat) / 6250000000000000000), LB := ((2308885118980919 : Rat) / 2000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2523065653 : Rat) / 1024000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((96259787 : Rat) / 1024000000), D3 := ((9215094822823660773 : Rat) / 50000000000000000000), D4 := ((3977667254813056787 : Rat) / 12500000000000000000), LB := ((10081297705646919 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((197230201 : Rat) / 80000000), R := ((12630137463 : Rat) / 5120000000), D0 := ((12630137463 : Rat) / 5120000000), D1 := ((3324664951 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9142784285714285773 : Rat) / 50000000000000000000), D4 := ((3959589620535713037 : Rat) / 12500000000000000000), LB := ((38836226718164113 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12630137463 : Rat) / 5120000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((466489737 : Rat) / 5120000000), D3 := ((9070473748604910773 : Rat) / 50000000000000000000), D4 := ((3941511986258369287 : Rat) / 12500000000000000000), LB := ((7039846146508211 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((12644946661 : Rat) / 5120000000), D0 := ((12644946661 : Rat) / 5120000000), D1 := ((3339474149 : Rat) / 5120000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((8998163211495535773 : Rat) / 50000000000000000000), D4 := ((3923434351981025537 : Rat) / 12500000000000000000), LB := ((419272066674381 : Rat) / 400000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12644946661 : Rat) / 5120000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 5120000000), D3 := ((8925852674386160773 : Rat) / 50000000000000000000), D4 := ((3905356717703681787 : Rat) / 12500000000000000000), LB := ((3553673087152709 : Rat) / 2500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((632617563 : Rat) / 256000000), R := ((12659755859 : Rat) / 5120000000), D0 := ((12659755859 : Rat) / 5120000000), D1 := ((3354283347 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((8853542137276785773 : Rat) / 50000000000000000000), D4 := ((3887279083426338037 : Rat) / 12500000000000000000), LB := ((2280491825608251 : Rat) / 1250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12659755859 : Rat) / 5120000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((436871341 : Rat) / 5120000000), D3 := ((8781231600167410773 : Rat) / 50000000000000000000), D4 := ((3869201449148994287 : Rat) / 12500000000000000000), LB := ((11287585358679547 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((8708921063058035773 : Rat) / 50000000000000000000), D4 := ((3851123814871650537 : Rat) / 12500000000000000000), LB := ((3825691652034613 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8564299988839285773 : Rat) / 50000000000000000000), D4 := ((3814968546316963037 : Rat) / 12500000000000000000), LB := ((14135882918678289 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((8419678914620535773 : Rat) / 50000000000000000000), D4 := ((3778813277762275537 : Rat) / 12500000000000000000), LB := ((25754139060358283 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8275057840401785773 : Rat) / 50000000000000000000), D4 := ((3742658009207588037 : Rat) / 12500000000000000000), LB := ((387378122037621 : Rat) / 100000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8130436766183035773 : Rat) / 50000000000000000000), D4 := ((3706502740652900537 : Rat) / 12500000000000000000), LB := ((1062997028504381 : Rat) / 200000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((7985815691964285773 : Rat) / 50000000000000000000), D4 := ((3670347472098213037 : Rat) / 12500000000000000000), LB := ((23224589379527427 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((7696573543526785773 : Rat) / 50000000000000000000), D4 := ((3598036934988838037 : Rat) / 12500000000000000000), LB := ((752132191393657 : Rat) / 125000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7407331395089285773 : Rat) / 50000000000000000000), D4 := ((3525726397879463037 : Rat) / 12500000000000000000), LB := ((3549221449745399 : Rat) / 2500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6828847098214285773 : Rat) / 50000000000000000000), D4 := ((3381105323660713037 : Rat) / 12500000000000000000), LB := ((1283937599769161 : Rat) / 100000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6250362801339285773 : Rat) / 50000000000000000000), D4 := ((3236484249441963037 : Rat) / 12500000000000000000), LB := ((894567539307679 : Rat) / 31250000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5671878504464285773 : Rat) / 50000000000000000000), D4 := ((3091863175223213037 : Rat) / 12500000000000000000), LB := ((1703950797968319 : Rat) / 50000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((511587 : Rat) / 200000), R := ((516101909910714285773 : Rat) / 200000000000000000000), D0 := ((516101909910714285773 : Rat) / 200000000000000000000), D1 := ((152606889910714285773 : Rat) / 200000000000000000000), D2 := ((4514909910714285773 : Rat) / 200000000000000000000), D3 := ((4514909910714285773 : Rat) / 50000000000000000000), D4 := ((2802621026785713037 : Rat) / 12500000000000000000), LB := ((28032583500843297 : Rat) / 500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((516101909910714285773 : Rat) / 200000000000000000000), R := ((260308409910714285773 : Rat) / 100000000000000000000), D0 := ((260308409910714285773 : Rat) / 100000000000000000000), D1 := ((78560899910714285773 : Rat) / 100000000000000000000), D2 := ((4514909910714285773 : Rat) / 100000000000000000000), D3 := ((13544729732142857319 : Rat) / 200000000000000000000), D4 := ((40327026517857122819 : Rat) / 200000000000000000000), LB := ((1528479458452623 : Rat) / 25000000000000000) }
]

def block395RightChunk000L : Rat := ((21750756696428571471 : Rat) / 12500000000000000000)
def block395RightChunk000R : Rat := ((260308409910714285773 : Rat) / 100000000000000000000)

def block395RightChunk000Certificate : Bool :=
  allBoxesValid block395RightChunk000 &&
  coversFromBool block395RightChunk000 block395RightChunk000L block395RightChunk000R

theorem block395RightChunk000Certificate_eq_true :
    block395RightChunk000Certificate = true := by
  native_decide

def block395RightChunk001 : List RatBox := [
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((260308409910714285773 : Rat) / 100000000000000000000), R := ((132411659910714285773 : Rat) / 50000000000000000000), D0 := ((132411659910714285773 : Rat) / 50000000000000000000), D1 := ((41537904910714285773 : Rat) / 50000000000000000000), D2 := ((4514909910714285773 : Rat) / 50000000000000000000), D3 := ((4514909910714285773 : Rat) / 100000000000000000000), D4 := ((17906058303571418523 : Rat) / 100000000000000000000), LB := ((14640539236315489 : Rat) / 250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((132411659910714285773 : Rat) / 50000000000000000000), R := ((67356115312500000057 : Rat) / 25000000000000000000), D0 := ((67356115312500000057 : Rat) / 25000000000000000000), D1 := ((21919237812500000057 : Rat) / 25000000000000000000), D2 := ((3407740312500000057 : Rat) / 25000000000000000000), D3 := ((2300570714285714341 : Rat) / 50000000000000000000), D4 := ((53564593571428531 : Rat) / 400000000000000000), LB := ((5183297125982131 : Rat) / 250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((67356115312500000057 : Rat) / 25000000000000000000), R := ((541149493214285714797 : Rat) / 200000000000000000000), D0 := ((541149493214285714797 : Rat) / 200000000000000000000), D1 := ((177654473214285714797 : Rat) / 200000000000000000000), D2 := ((29562493214285714797 : Rat) / 200000000000000000000), D3 := ((2300570714285714341 : Rat) / 40000000000000000000), D4 := ((2197501741071426017 : Rat) / 25000000000000000000), LB := ((643473567165119 : Rat) / 25000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((541149493214285714797 : Rat) / 200000000000000000000), R := ((216919911428571428787 : Rat) / 80000000000000000000), D0 := ((216919911428571428787 : Rat) / 80000000000000000000), D1 := ((71521903428571428787 : Rat) / 80000000000000000000), D2 := ((12285111428571428787 : Rat) / 80000000000000000000), D3 := ((25306277857142857751 : Rat) / 400000000000000000000), D4 := ((3055888642857138759 : Rat) / 40000000000000000000), LB := ((20938319573278963 : Rat) / 1000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((216919911428571428787 : Rat) / 80000000000000000000), R := ((271725031964285714569 : Rat) / 100000000000000000000), D0 := ((271725031964285714569 : Rat) / 100000000000000000000), D1 := ((89977521964285714569 : Rat) / 100000000000000000000), D2 := ((15931531964285714569 : Rat) / 100000000000000000000), D3 := ((6901712142857143023 : Rat) / 100000000000000000000), D4 := ((28258315714285673249 : Rat) / 400000000000000000000), LB := ((860635895224593 : Rat) / 100000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((271725031964285714569 : Rat) / 100000000000000000000), R := ((2176100826428571430893 : Rat) / 800000000000000000000), D0 := ((2176100826428571430893 : Rat) / 800000000000000000000), D1 := ((722120746428571430893 : Rat) / 800000000000000000000), D2 := ((129752826428571430893 : Rat) / 800000000000000000000), D3 := ((2300570714285714341 : Rat) / 32000000000000000000), D4 := ((6489436249999989727 : Rat) / 100000000000000000000), LB := ((4814902485850897 : Rat) / 500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2176100826428571430893 : Rat) / 800000000000000000000), R := ((1089200698571428572617 : Rat) / 400000000000000000000), D0 := ((1089200698571428572617 : Rat) / 400000000000000000000), D1 := ((362210658571428572617 : Rat) / 400000000000000000000), D2 := ((66026698571428572617 : Rat) / 400000000000000000000), D3 := ((29907419285714286433 : Rat) / 400000000000000000000), D4 := ((1984596771428568139 : Rat) / 32000000000000000000), LB := ((5165223733265167 : Rat) / 1000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1089200698571428572617 : Rat) / 400000000000000000000), R := ((87228078714285714383 : Rat) / 32000000000000000000), D0 := ((87228078714285714383 : Rat) / 32000000000000000000), D1 := ((29068875514285714383 : Rat) / 32000000000000000000), D2 := ((5374158714285714383 : Rat) / 32000000000000000000), D3 := ((62115409285714287207 : Rat) / 800000000000000000000), D4 := ((23657174285714244567 : Rat) / 400000000000000000000), LB := ((12925168960828959 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((87228078714285714383 : Rat) / 32000000000000000000), R := ((4363704506428571433491 : Rat) / 1600000000000000000000), D0 := ((4363704506428571433491 : Rat) / 1600000000000000000000), D1 := ((1455744346428571433491 : Rat) / 1600000000000000000000), D2 := ((271008506428571433491 : Rat) / 1600000000000000000000), D3 := ((25306277857142857751 : Rat) / 320000000000000000000), D4 := ((45013777857142774793 : Rat) / 800000000000000000000), LB := ((817425284667897 : Rat) / 250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4363704506428571433491 : Rat) / 1600000000000000000000), R := ((545750634642857143479 : Rat) / 200000000000000000000), D0 := ((545750634642857143479 : Rat) / 200000000000000000000), D1 := ((182255614642857143479 : Rat) / 200000000000000000000), D2 := ((34163634642857143479 : Rat) / 200000000000000000000), D3 := ((16103995000000000387 : Rat) / 200000000000000000000), D4 := ((17545396999999967049 : Rat) / 320000000000000000000), LB := ((18074558017228681 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((545750634642857143479 : Rat) / 200000000000000000000), R := ((4368305647857142862173 : Rat) / 1600000000000000000000), D0 := ((4368305647857142862173 : Rat) / 1600000000000000000000), D1 := ((1460345487857142862173 : Rat) / 1600000000000000000000), D2 := ((275609647857142862173 : Rat) / 1600000000000000000000), D3 := ((131132530714285717437 : Rat) / 1600000000000000000000), D4 := ((10678301785714265113 : Rat) / 200000000000000000000), LB := ((40480783628567 : Rat) / 80000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4368305647857142862173 : Rat) / 1600000000000000000000), R := ((8738911866428571438687 : Rat) / 3200000000000000000000), D0 := ((8738911866428571438687 : Rat) / 3200000000000000000000), D1 := ((2922991546428571438687 : Rat) / 3200000000000000000000), D2 := ((553519866428571438687 : Rat) / 3200000000000000000000), D3 := ((52913126428571429843 : Rat) / 640000000000000000000), D4 := ((83125843571428406563 : Rat) / 1600000000000000000000), LB := ((481328558456659 : Rat) / 250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8738911866428571438687 : Rat) / 3200000000000000000000), R := ((2185303109285714288257 : Rat) / 800000000000000000000), D0 := ((2185303109285714288257 : Rat) / 800000000000000000000), D1 := ((731323029285714288257 : Rat) / 800000000000000000000), D2 := ((138955109285714288257 : Rat) / 800000000000000000000), D3 := ((66716550714285715889 : Rat) / 800000000000000000000), D4 := ((32790223285714219757 : Rat) / 640000000000000000000), LB := ((7027608729444357 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2185303109285714288257 : Rat) / 800000000000000000000), R := ((8743513007857142867369 : Rat) / 3200000000000000000000), D0 := ((8743513007857142867369 : Rat) / 3200000000000000000000), D1 := ((2927592687857142867369 : Rat) / 3200000000000000000000), D2 := ((558121007857142867369 : Rat) / 3200000000000000000000), D3 := ((269166773571428577897 : Rat) / 3200000000000000000000), D4 := ((40412636428571346111 : Rat) / 800000000000000000000), LB := ((4643054036941041 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8743513007857142867369 : Rat) / 3200000000000000000000), R := ((874581357857142858171 : Rat) / 320000000000000000000), D0 := ((874581357857142858171 : Rat) / 320000000000000000000), D1 := ((292989325857142858171 : Rat) / 320000000000000000000), D2 := ((56042157857142858171 : Rat) / 320000000000000000000), D3 := ((135733672142857146119 : Rat) / 1600000000000000000000), D4 := ((159349974999999670103 : Rat) / 3200000000000000000000), LB := ((123795356480369 : Rat) / 250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((874581357857142858171 : Rat) / 320000000000000000000), R := ((8748114149285714296051 : Rat) / 3200000000000000000000), D0 := ((8748114149285714296051 : Rat) / 3200000000000000000000), D1 := ((2932193829285714296051 : Rat) / 3200000000000000000000), D2 := ((562722149285714296051 : Rat) / 3200000000000000000000), D3 := ((273767915000000006579 : Rat) / 3200000000000000000000), D4 := ((78524702142856977881 : Rat) / 1600000000000000000000), LB := ((10587521496080443 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8748114149285714296051 : Rat) / 3200000000000000000000), R := ((17498528869285714306443 : Rat) / 6400000000000000000000), D0 := ((17498528869285714306443 : Rat) / 6400000000000000000000), D1 := ((5866688229285714306443 : Rat) / 6400000000000000000000), D2 := ((1127744869285714306443 : Rat) / 6400000000000000000000), D3 := ((549836400714285727499 : Rat) / 6400000000000000000000), D4 := ((154748833571428241421 : Rat) / 3200000000000000000000), LB := ((5051947787936273 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17498528869285714306443 : Rat) / 6400000000000000000000), R := ((1093801840000000001299 : Rat) / 400000000000000000000), D0 := ((1093801840000000001299 : Rat) / 400000000000000000000), D1 := ((366811800000000001299 : Rat) / 400000000000000000000), D2 := ((70627840000000001299 : Rat) / 400000000000000000000), D3 := ((6901712142857143023 : Rat) / 80000000000000000000), D4 := ((307197096428570768501 : Rat) / 6400000000000000000000), LB := ((851862132754011 : Rat) / 1000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1093801840000000001299 : Rat) / 400000000000000000000), R := ((140025040085714285881 : Rat) / 51200000000000000000), D0 := ((140025040085714285881 : Rat) / 51200000000000000000), D1 := ((46970314965714285881 : Rat) / 51200000000000000000), D2 := ((9058768085714285881 : Rat) / 51200000000000000000), D3 := ((554437542142857156181 : Rat) / 6400000000000000000000), D4 := ((3811206571428563177 : Rat) / 80000000000000000000), LB := ((352420079575283 : Rat) / 500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((140025040085714285881 : Rat) / 51200000000000000000), R := ((8752715290714285724733 : Rat) / 3200000000000000000000), D0 := ((8752715290714285724733 : Rat) / 3200000000000000000000), D1 := ((2936794970714285724733 : Rat) / 3200000000000000000000), D2 := ((567323290714285724733 : Rat) / 3200000000000000000000), D3 := ((278369056428571435261 : Rat) / 3200000000000000000000), D4 := ((302595954999999339819 : Rat) / 6400000000000000000000), LB := ((2847110920903839 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8752715290714285724733 : Rat) / 3200000000000000000000), R := ((17507731152142857163807 : Rat) / 6400000000000000000000), D0 := ((17507731152142857163807 : Rat) / 6400000000000000000000), D1 := ((5875890512142857163807 : Rat) / 6400000000000000000000), D2 := ((1136947152142857163807 : Rat) / 6400000000000000000000), D3 := ((559038683571428584863 : Rat) / 6400000000000000000000), D4 := ((150147692142856812739 : Rat) / 3200000000000000000000), LB := ((22285495496898733 : Rat) / 50000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17507731152142857163807 : Rat) / 6400000000000000000000), R := ((4377507930714285719537 : Rat) / 1600000000000000000000), D0 := ((4377507930714285719537 : Rat) / 1600000000000000000000), D1 := ((1469547770714285719537 : Rat) / 1600000000000000000000), D2 := ((284811930714285719537 : Rat) / 1600000000000000000000), D3 := ((140334813571428574801 : Rat) / 1600000000000000000000), D4 := ((297994813571427911137 : Rat) / 6400000000000000000000), LB := ((33380827556789283 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4377507930714285719537 : Rat) / 1600000000000000000000), R := ((17512332293571428592489 : Rat) / 6400000000000000000000), D0 := ((17512332293571428592489 : Rat) / 6400000000000000000000), D1 := ((5880491653571428592489 : Rat) / 6400000000000000000000), D2 := ((1141548293571428592489 : Rat) / 6400000000000000000000), D3 := ((112727965000000002709 : Rat) / 1280000000000000000000), D4 := ((73923560714285549199 : Rat) / 1600000000000000000000), LB := ((4676510863187433 : Rat) / 20000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17512332293571428592489 : Rat) / 6400000000000000000000), R := ((1751463286428571430683 : Rat) / 640000000000000000000), D0 := ((1751463286428571430683 : Rat) / 640000000000000000000), D1 := ((588279222428571430683 : Rat) / 640000000000000000000), D2 := ((114384886428571430683 : Rat) / 640000000000000000000), D3 := ((282970197857142863943 : Rat) / 3200000000000000000000), D4 := ((58678734428571296491 : Rat) / 1280000000000000000000), LB := ((3646834681132749 : Rat) / 25000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1751463286428571430683 : Rat) / 640000000000000000000), R := ((17516933435000000021171 : Rat) / 6400000000000000000000), D0 := ((17516933435000000021171 : Rat) / 6400000000000000000000), D1 := ((5885092795000000021171 : Rat) / 6400000000000000000000), D2 := ((1146149435000000021171 : Rat) / 6400000000000000000000), D3 := ((568240966428571442227 : Rat) / 6400000000000000000000), D4 := ((145546550714285384057 : Rat) / 3200000000000000000000), LB := ((875837351863723 : Rat) / 12500000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17516933435000000021171 : Rat) / 6400000000000000000000), R := ((2189904250714285716939 : Rat) / 800000000000000000000), D0 := ((2189904250714285716939 : Rat) / 800000000000000000000), D1 := ((735924170714285716939 : Rat) / 800000000000000000000), D2 := ((143556250714285716939 : Rat) / 800000000000000000000), D3 := ((71317692142857144571 : Rat) / 800000000000000000000), D4 := ((288792530714285053773 : Rat) / 6400000000000000000000), LB := ((26100517212857 : Rat) / 4000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2189904250714285716939 : Rat) / 800000000000000000000), R := ((7008153716428571437073 : Rat) / 2560000000000000000000), D0 := ((7008153716428571437073 : Rat) / 2560000000000000000000), D1 := ((2355417460428571437073 : Rat) / 2560000000000000000000), D2 := ((459840116428571437073 : Rat) / 2560000000000000000000), D3 := ((1143383645000000027477 : Rat) / 12800000000000000000000), D4 := ((35811494999999917429 : Rat) / 800000000000000000000), LB := ((2825254042579939 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((7008153716428571437073 : Rat) / 2560000000000000000000), R := ((17521534576428571449853 : Rat) / 6400000000000000000000), D0 := ((17521534576428571449853 : Rat) / 6400000000000000000000), D1 := ((5889693936428571449853 : Rat) / 6400000000000000000000), D2 := ((1150750576428571449853 : Rat) / 6400000000000000000000), D3 := ((572842107857142870909 : Rat) / 6400000000000000000000), D4 := ((570683349285712964523 : Rat) / 12800000000000000000000), LB := ((2716928872485147 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17521534576428571449853 : Rat) / 6400000000000000000000), R := ((35045369723571428614047 : Rat) / 12800000000000000000000), D0 := ((35045369723571428614047 : Rat) / 12800000000000000000000), D1 := ((11781688443571428614047 : Rat) / 12800000000000000000000), D2 := ((2303801723571428614047 : Rat) / 12800000000000000000000), D3 := ((1147984786428571456159 : Rat) / 12800000000000000000000), D4 := ((284191389285713625091 : Rat) / 6400000000000000000000), LB := ((2624340231281719 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35045369723571428614047 : Rat) / 12800000000000000000000), R := ((8761917573571428582097 : Rat) / 3200000000000000000000), D0 := ((8761917573571428582097 : Rat) / 3200000000000000000000), D1 := ((2945997253571428582097 : Rat) / 3200000000000000000000), D2 := ((576525573571428582097 : Rat) / 3200000000000000000000), D3 := ((2300570714285714341 : Rat) / 25600000000000000000), D4 := ((566082207857141535841 : Rat) / 12800000000000000000000), LB := ((2547570038211877 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8761917573571428582097 : Rat) / 3200000000000000000000), R := ((35049970865000000042729 : Rat) / 12800000000000000000000), D0 := ((35049970865000000042729 : Rat) / 12800000000000000000000), D1 := ((11786289585000000042729 : Rat) / 12800000000000000000000), D2 := ((2308402865000000042729 : Rat) / 12800000000000000000000), D3 := ((1152585927857142884841 : Rat) / 12800000000000000000000), D4 := ((1127563274285711643 : Rat) / 25600000000000000000), LB := ((4973402948565409 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35049970865000000042729 : Rat) / 12800000000000000000000), R := ((3505227143571428575707 : Rat) / 1280000000000000000000), D0 := ((3505227143571428575707 : Rat) / 1280000000000000000000), D1 := ((1178859015571428575707 : Rat) / 1280000000000000000000), D2 := ((231070343571428575707 : Rat) / 1280000000000000000000), D3 := ((577443249285714299591 : Rat) / 6400000000000000000000), D4 := ((561481066428570107159 : Rat) / 12800000000000000000000), LB := ((4883638001696999 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3505227143571428575707 : Rat) / 1280000000000000000000), R := ((35054572006428571471411 : Rat) / 12800000000000000000000), D0 := ((35054572006428571471411 : Rat) / 12800000000000000000000), D1 := ((11790890726428571471411 : Rat) / 12800000000000000000000), D2 := ((2313004006428571471411 : Rat) / 12800000000000000000000), D3 := ((1157187069285714313523 : Rat) / 12800000000000000000000), D4 := ((279590247857142196409 : Rat) / 6400000000000000000000), LB := ((4826016757200069 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35054572006428571471411 : Rat) / 12800000000000000000000), R := ((4382109072142857148219 : Rat) / 1600000000000000000000), D0 := ((4382109072142857148219 : Rat) / 1600000000000000000000), D1 := ((1474148912142857148219 : Rat) / 1600000000000000000000), D2 := ((289413072142857148219 : Rat) / 1600000000000000000000), D3 := ((144935955000000003483 : Rat) / 1600000000000000000000), D4 := ((556879924999998678477 : Rat) / 12800000000000000000000), LB := ((4800713373876997 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4382109072142857148219 : Rat) / 1600000000000000000000), R := ((35059173147857142900093 : Rat) / 12800000000000000000000), D0 := ((35059173147857142900093 : Rat) / 12800000000000000000000), D1 := ((11795491867857142900093 : Rat) / 12800000000000000000000), D2 := ((2317605147857142900093 : Rat) / 12800000000000000000000), D3 := ((232357642142857148441 : Rat) / 2560000000000000000000), D4 := ((69322419285714120517 : Rat) / 1600000000000000000000), LB := ((48079046875920683 : Rat) / 100000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35059173147857142900093 : Rat) / 12800000000000000000000), R := ((17530736859285714307217 : Rat) / 6400000000000000000000), D0 := ((17530736859285714307217 : Rat) / 6400000000000000000000), D1 := ((5898896219285714307217 : Rat) / 6400000000000000000000), D2 := ((1159952859285714307217 : Rat) / 6400000000000000000000), D3 := ((582044390714285728273 : Rat) / 6400000000000000000000), D4 := ((110455756714285449959 : Rat) / 2560000000000000000000), LB := ((24238851258809313 : Rat) / 50000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17530736859285714307217 : Rat) / 6400000000000000000000), R := ((1402550971571428573151 : Rat) / 512000000000000000000), D0 := ((1402550971571428573151 : Rat) / 512000000000000000000), D1 := ((472003720371428573151 : Rat) / 512000000000000000000), D2 := ((92888251571428573151 : Rat) / 512000000000000000000), D3 := ((1166389352142857170887 : Rat) / 12800000000000000000000), D4 := ((274989106428570767727 : Rat) / 6400000000000000000000), LB := ((2460246189381621 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1402550971571428573151 : Rat) / 512000000000000000000), R := ((8766518715000000010779 : Rat) / 3200000000000000000000), D0 := ((8766518715000000010779 : Rat) / 3200000000000000000000), D1 := ((2950598395000000010779 : Rat) / 3200000000000000000000), D2 := ((581126715000000010779 : Rat) / 3200000000000000000000), D3 := ((292172480714285721307 : Rat) / 3200000000000000000000), D4 := ((547677642142855821113 : Rat) / 12800000000000000000000), LB := ((2513128091051753 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8766518715000000010779 : Rat) / 3200000000000000000000), R := ((35068375430714285757457 : Rat) / 12800000000000000000000), D0 := ((35068375430714285757457 : Rat) / 12800000000000000000000), D1 := ((11804694150714285757457 : Rat) / 12800000000000000000000), D2 := ((2326807430714285757457 : Rat) / 12800000000000000000000), D3 := ((1170990493571428599569 : Rat) / 12800000000000000000000), D4 := ((136344267857142526693 : Rat) / 3200000000000000000000), LB := ((645656202475503 : Rat) / 1250000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35068375430714285757457 : Rat) / 12800000000000000000000), R := ((17535338000714285735899 : Rat) / 6400000000000000000000), D0 := ((17535338000714285735899 : Rat) / 6400000000000000000000), D1 := ((5903497360714285735899 : Rat) / 6400000000000000000000), D2 := ((1164554000714285735899 : Rat) / 6400000000000000000000), D3 := ((117329106428571431391 : Rat) / 1280000000000000000000), D4 := ((543076500714284392431 : Rat) / 12800000000000000000000), LB := ((5337663538387827 : Rat) / 10000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17535338000714285735899 : Rat) / 6400000000000000000000), R := ((35072976572142857186139 : Rat) / 12800000000000000000000), D0 := ((35072976572142857186139 : Rat) / 12800000000000000000000), D1 := ((11809295292142857186139 : Rat) / 12800000000000000000000), D2 := ((2331408572142857186139 : Rat) / 12800000000000000000000), D3 := ((1175591635000000028251 : Rat) / 12800000000000000000000), D4 := ((54077592999999867809 : Rat) / 1280000000000000000000), LB := ((2771845859054489 : Rat) / 5000000000000000000) },
  { w1 := ((1998300862821083 : Rat) / 2500000000000000), w2 := ((811657153415767 : Rat) / 20000000000000000), w3 := ((17278939343102073 : Rat) / 100000000000000000), w4 := ((1461578951266487 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132411659910714285773 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35072976572142857186139 : Rat) / 12800000000000000000000), R := ((27402560267857142891 : Rat) / 10000000000000000000), D0 := ((27402560267857142891 : Rat) / 10000000000000000000), D1 := ((9227809267857142891 : Rat) / 10000000000000000000), D2 := ((1823210267857142891 : Rat) / 10000000000000000000), D3 := ((2300570714285714341 : Rat) / 25000000000000000000), D4 := ((538475359285712963749 : Rat) / 12800000000000000000000), LB := ((2891765459546447 : Rat) / 5000000000000000000) }
]

def block395RightChunk001L : Rat := ((260308409910714285773 : Rat) / 100000000000000000000)
def block395RightChunk001R : Rat := ((27402560267857142891 : Rat) / 10000000000000000000)

def block395RightChunk001Certificate : Bool :=
  allBoxesValid block395RightChunk001 &&
  coversFromBool block395RightChunk001 block395RightChunk001L block395RightChunk001R

theorem block395RightChunk001Certificate_eq_true :
    block395RightChunk001Certificate = true := by
  native_decide

def block395RightChainCertificate : Bool :=
  decide (
    block395RightL = ((21750756696428571471 : Rat) / 12500000000000000000) /\
    ((260308409910714285773 : Rat) / 100000000000000000000) = ((260308409910714285773 : Rat) / 100000000000000000000) /\
    ((27402560267857142891 : Rat) / 10000000000000000000) = block395RightR)

theorem block395RightChainCertificate_eq_true :
    block395RightChainCertificate = true := by
  native_decide

def block395LeftBoxCount : Nat := boxCount block395LeftBoxes
def block395RightBoxCount : Nat := 142

def block395_rational_certificate : Prop :=
    block395LeftCertificate = true /\
    block395RightChainCertificate = true /\
    block395RightChunk000Certificate = true /\
    block395RightChunk001Certificate = true

theorem block395_rational_certificate_proof :
    block395_rational_certificate := by
  exact ⟨block395LeftCertificate_eq_true, block395RightChainCertificate_eq_true, block395RightChunk000Certificate_eq_true, block395RightChunk001Certificate_eq_true⟩

end Block395
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block395

open Set

def block395W1 : Rat := ((1998300862821083 : Rat) / 2500000000000000)
def block395W2 : Rat := ((811657153415767 : Rat) / 20000000000000000)
def block395W3 : Rat := ((17278939343102073 : Rat) / 100000000000000000)
def block395W4 : Rat := ((1461578951266487 : Rat) / 10000000000000000)
def block395S1 : Rat := ((18174751 : Rat) / 10000000)
def block395S2 : Rat := ((511587 : Rat) / 200000)
def block395S3 : Rat := ((132411659910714285773 : Rat) / 50000000000000000000)
def block395S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block395V (y : ℝ) : ℝ :=
  ratPotential block395W1 block395W2 block395W3 block395W4 block395S1 block395S2 block395S3 block395S4 y

def block395LeftParamsCertificate : Bool :=
  allBoxesSameParams block395LeftBoxes block395W1 block395W2 block395W3 block395W4 block395S1 block395S2 block395S3 block395S4

theorem block395LeftParamsCertificate_eq_true :
    block395LeftParamsCertificate = true := by
  native_decide

theorem block395_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block395LeftL : ℝ) (block395LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block395S1 : ℝ))
    (hy2ne : y ≠ (block395S2 : ℝ))
    (hy3ne : y ≠ (block395S3 : ℝ))
    (hy4ne : y ≠ (block395S4 : ℝ)) :
    0 < block395V y := by
  have hcert := block395LeftCertificate_eq_true
  unfold block395LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block395LeftBoxes) (lo := block395LeftL) (hi := block395LeftR)
    (w1 := block395W1) (w2 := block395W2) (w3 := block395W3) (w4 := block395W4)
    (s1 := block395S1) (s2 := block395S2) (s3 := block395S3) (s4 := block395S4)
    hboxes hcover block395LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block395RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block395RightChunk000 block395W1 block395W2 block395W3 block395W4 block395S1 block395S2 block395S3 block395S4

theorem block395RightChunk000ParamsCertificate_eq_true :
    block395RightChunk000ParamsCertificate = true := by
  native_decide

theorem block395_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block395RightChunk000L : ℝ) (block395RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block395S1 : ℝ))
    (hy2ne : y ≠ (block395S2 : ℝ))
    (hy3ne : y ≠ (block395S3 : ℝ))
    (hy4ne : y ≠ (block395S4 : ℝ)) :
    0 < block395V y := by
  have hcert := block395RightChunk000Certificate_eq_true
  unfold block395RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block395RightChunk000) (lo := block395RightChunk000L) (hi := block395RightChunk000R)
    (w1 := block395W1) (w2 := block395W2) (w3 := block395W3) (w4 := block395W4)
    (s1 := block395S1) (s2 := block395S2) (s3 := block395S3) (s4 := block395S4)
    hboxes hcover block395RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block395RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block395RightChunk001 block395W1 block395W2 block395W3 block395W4 block395S1 block395S2 block395S3 block395S4

theorem block395RightChunk001ParamsCertificate_eq_true :
    block395RightChunk001ParamsCertificate = true := by
  native_decide

theorem block395_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block395RightChunk001L : ℝ) (block395RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block395S1 : ℝ))
    (hy2ne : y ≠ (block395S2 : ℝ))
    (hy3ne : y ≠ (block395S3 : ℝ))
    (hy4ne : y ≠ (block395S4 : ℝ)) :
    0 < block395V y := by
  have hcert := block395RightChunk001Certificate_eq_true
  unfold block395RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block395RightChunk001) (lo := block395RightChunk001L) (hi := block395RightChunk001R)
    (w1 := block395W1) (w2 := block395W2) (w3 := block395W3) (w4 := block395W4)
    (s1 := block395S1) (s2 := block395S2) (s3 := block395S3) (s4 := block395S4)
    hboxes hcover block395RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block395_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block395RightL : ℝ) (block395RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block395S1 : ℝ))
    (hy2ne : y ≠ (block395S2 : ℝ))
    (hy3ne : y ≠ (block395S3 : ℝ))
    (hy4ne : y ≠ (block395S4 : ℝ)) :
    0 < block395V y := by
  by_cases h0 : y ≤ (block395RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block395RightChunk000L : ℝ) (block395RightChunk000R : ℝ) := by
      have hL : (block395RightChunk000L : ℝ) = (block395RightL : ℝ) := by
        norm_num [block395RightChunk000L, block395RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block395_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block395RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block395RightChunk001L : ℝ) = (block395RightChunk000R : ℝ) := by
      norm_num [block395RightChunk001L, block395RightChunk000R]
    have hR : (block395RightChunk001R : ℝ) = (block395RightR : ℝ) := by
      norm_num [block395RightChunk001R, block395RightR]
    have hyc : y ∈ Icc (block395RightChunk001L : ℝ) (block395RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block395_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block395_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block395LeftL : ℝ) (block395LeftR : ℝ) →
    y ≠ 0 → y ≠ (block395S1 : ℝ) → y ≠ (block395S2 : ℝ) →
    y ≠ (block395S3 : ℝ) → y ≠ (block395S4 : ℝ) → 0 < block395V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block395RightL : ℝ) (block395RightR : ℝ) →
    y ≠ 0 → y ≠ (block395S1 : ℝ) → y ≠ (block395S2 : ℝ) →
    y ≠ (block395S3 : ℝ) → y ≠ (block395S4 : ℝ) → 0 < block395V y)

theorem block395_reallog_certificate_proof :
    block395_reallog_certificate := by
  exact ⟨block395_left_V_pos, block395_right_V_pos⟩

end Block395
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block395.block395V
#check Erdos1038Lean.M1817475.Block395.block395_left_V_pos
#check Erdos1038Lean.M1817475.Block395.block395_right_V_pos
#check Erdos1038Lean.M1817475.Block395.block395_reallog_certificate_proof
