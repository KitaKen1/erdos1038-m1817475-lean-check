/-
Self-contained Lean4Web paste file.
Block 390 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block390

def block390LeftL : Rat := ((37051899553571428739 : Rat) / 50000000000000000000)
def block390LeftR : Rat := ((3706167410714285731 : Rat) / 5000000000000000000)
def block390RightL : Rat := ((87051899553571428739 : Rat) / 50000000000000000000)
def block390RightR : Rat := ((13706167410714285731 : Rat) / 5000000000000000000)

def block390LeftBoxes : List RatBox := [
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((37051899553571428739 : Rat) / 50000000000000000000), R := ((3706167410714285731 : Rat) / 5000000000000000000), D0 := ((3706167410714285731 : Rat) / 5000000000000000000), D1 := ((53821855446428571261 : Rat) / 50000000000000000000), D2 := ((90844850446428571261 : Rat) / 50000000000000000000), D3 := ((11932188236607142843 : Rat) / 6250000000000000000), D4 := ((102055334553571423409 : Rat) / 50000000000000000000), LB := ((8093183205541421 : Rat) / 10000000000000000000) }
]

def block390LeftCertificate : Bool :=
  allBoxesValid block390LeftBoxes &&
  coversFromBool block390LeftBoxes block390LeftL block390LeftR

theorem block390LeftCertificate_eq_true :
    block390LeftCertificate = true := by
  native_decide

def block390RightChunk000 : List RatBox := [
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((87051899553571428739 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3821855446428571261 : Rat) / 50000000000000000000), D2 := ((40844850446428571261 : Rat) / 50000000000000000000), D3 := ((5682188236607142843 : Rat) / 6250000000000000000), D4 := ((52055334553571423409 : Rat) / 50000000000000000000), LB := ((3739652225779937 : Rat) / 2500000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41635650446428571483 : Rat) / 50000000000000000000), D4 := ((12058369776785713037 : Rat) / 12500000000000000000), LB := ((1694174696873171 : Rat) / 25000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23124152946428571483 : Rat) / 50000000000000000000), D4 := ((7430495401785713037 : Rat) / 12500000000000000000), LB := ((11504749603231071 : Rat) / 250000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18496278571428571483 : Rat) / 50000000000000000000), D4 := ((6273526808035713037 : Rat) / 12500000000000000000), LB := ((1187578945121219 : Rat) / 50000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16182341383928571483 : Rat) / 50000000000000000000), D4 := ((5695042511160713037 : Rat) / 12500000000000000000), LB := ((22465868113188597 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((15025372790178571483 : Rat) / 50000000000000000000), D4 := ((5405800362723213037 : Rat) / 12500000000000000000), LB := ((14782452347755423 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13868404196428571483 : Rat) / 50000000000000000000), D4 := ((5116558214285713037 : Rat) / 12500000000000000000), LB := ((4015773206672027 : Rat) / 500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((13289919899553571483 : Rat) / 50000000000000000000), D4 := ((4971937140066963037 : Rat) / 12500000000000000000), LB := ((4971458117 : Rat) / 4882812500000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((766707007 : Rat) / 320000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12711435602678571483 : Rat) / 50000000000000000000), D4 := ((4827316065848213037 : Rat) / 12500000000000000000), LB := ((2134752143151053 : Rat) / 400000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((12422193454241071483 : Rat) / 50000000000000000000), D4 := ((4755005528738838037 : Rat) / 12500000000000000000), LB := ((13089950602954703 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12132951305803571483 : Rat) / 50000000000000000000), D4 := ((4682694991629463037 : Rat) / 12500000000000000000), LB := ((8273460869240301 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((123561673 : Rat) / 51200000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11843709157366071483 : Rat) / 50000000000000000000), D4 := ((4610384454520088037 : Rat) / 12500000000000000000), LB := ((1536197548510157 : Rat) / 500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((11699088083147321483 : Rat) / 50000000000000000000), D4 := ((4574229185965400537 : Rat) / 12500000000000000000), LB := ((20694109587757747 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((387055803 : Rat) / 160000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11554467008928571483 : Rat) / 50000000000000000000), D4 := ((4538073917410713037 : Rat) / 12500000000000000000), LB := ((5694599670755529 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((11409845934709821483 : Rat) / 50000000000000000000), D4 := ((4501918648856025537 : Rat) / 12500000000000000000), LB := ((176417272738337 : Rat) / 625000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11265224860491071483 : Rat) / 50000000000000000000), D4 := ((4465763380301338037 : Rat) / 12500000000000000000), LB := ((5027242367522597 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((11192914323381696483 : Rat) / 50000000000000000000), D4 := ((4447685746023994287 : Rat) / 12500000000000000000), LB := ((8220036887599397 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((11120603786272321483 : Rat) / 50000000000000000000), D4 := ((4429608111746650537 : Rat) / 12500000000000000000), LB := ((3241317789457951 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((11048293249162946483 : Rat) / 50000000000000000000), D4 := ((4411530477469306787 : Rat) / 12500000000000000000), LB := ((1937316779458631 : Rat) / 2000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((81450589 : Rat) / 640000000), D3 := ((10975982712053571483 : Rat) / 50000000000000000000), D4 := ((4393452843191963037 : Rat) / 12500000000000000000), LB := ((6606094262484319 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((10903672174944196483 : Rat) / 50000000000000000000), D4 := ((4375375208914619287 : Rat) / 12500000000000000000), LB := ((745189349193931 : Rat) / 2000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10831361637834821483 : Rat) / 50000000000000000000), D4 := ((4357297574637275537 : Rat) / 12500000000000000000), LB := ((5241752074081063 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((24941877169 : Rat) / 10240000000), D0 := ((24941877169 : Rat) / 10240000000), D1 := ((1266186429 : Rat) / 2048000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((10759051100725446483 : Rat) / 50000000000000000000), D4 := ((4339219940359931787 : Rat) / 12500000000000000000), LB := ((1097477887826187 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24941877169 : Rat) / 10240000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((1251377231 : Rat) / 10240000000), D3 := ((10722895832170758983 : Rat) / 50000000000000000000), D4 := ((541272640402657489 : Rat) / 1562500000000000000), LB := ((9804043068486201 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((24956686367 : Rat) / 10240000000), D0 := ((24956686367 : Rat) / 10240000000), D1 := ((6345741343 : Rat) / 10240000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10686740563616071483 : Rat) / 50000000000000000000), D4 := ((4321142306082588037 : Rat) / 12500000000000000000), LB := ((2171356386037951 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24956686367 : Rat) / 10240000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((1236568033 : Rat) / 10240000000), D3 := ((10650585295061383983 : Rat) / 50000000000000000000), D4 := ((2156051744471958081 : Rat) / 6250000000000000000), LB := ((7619230771912511 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((4994299113 : Rat) / 2048000000), D0 := ((4994299113 : Rat) / 2048000000), D1 := ((6360550541 : Rat) / 10240000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((10614430026506696483 : Rat) / 50000000000000000000), D4 := ((4303064671805244287 : Rat) / 12500000000000000000), LB := ((6605767924313111 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4994299113 : Rat) / 2048000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((244351767 : Rat) / 2048000000), D3 := ((10578274757952008983 : Rat) / 50000000000000000000), D4 := ((1073506463666643103 : Rat) / 3125000000000000000), LB := ((1129070194825943 : Rat) / 2000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((24986304763 : Rat) / 10240000000), D0 := ((24986304763 : Rat) / 10240000000), D1 := ((6375359739 : Rat) / 10240000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10542119489397321483 : Rat) / 50000000000000000000), D4 := ((4284987037527900537 : Rat) / 12500000000000000000), LB := ((2961436744611419 : Rat) / 6250000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((24986304763 : Rat) / 10240000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((1206949637 : Rat) / 10240000000), D3 := ((10505964220842633983 : Rat) / 50000000000000000000), D4 := ((2137974110194614331 : Rat) / 6250000000000000000), LB := ((38849352429157213 : Rat) / 100000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((25001113961 : Rat) / 10240000000), D0 := ((25001113961 : Rat) / 10240000000), D1 := ((6390168937 : Rat) / 10240000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((10469808952287946483 : Rat) / 50000000000000000000), D4 := ((4266909403250556787 : Rat) / 12500000000000000000), LB := ((6171178589889359 : Rat) / 20000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25001113961 : Rat) / 10240000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((1192140439 : Rat) / 10240000000), D3 := ((10433653683733258983 : Rat) / 50000000000000000000), D4 := ((266116911631992807 : Rat) / 781250000000000000), LB := ((11702975591711129 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((156303241 : Rat) / 64000000), R := ((25015923159 : Rat) / 10240000000), D0 := ((25015923159 : Rat) / 10240000000), D1 := ((1280995627 : Rat) / 2048000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10397498415178571483 : Rat) / 50000000000000000000), D4 := ((4248831768973213037 : Rat) / 12500000000000000000), LB := ((16502921970334983 : Rat) / 100000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25015923159 : Rat) / 10240000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((1177331241 : Rat) / 10240000000), D3 := ((10361343146623883983 : Rat) / 50000000000000000000), D4 := ((2119896475917270581 : Rat) / 6250000000000000000), LB := ((507512719704617 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((25030732357 : Rat) / 10240000000), D0 := ((25030732357 : Rat) / 10240000000), D1 := ((6419787333 : Rat) / 10240000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((10325187878069196483 : Rat) / 50000000000000000000), D4 := ((4230754134695869287 : Rat) / 12500000000000000000), LB := ((10878632325357629 : Rat) / 250000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25030732357 : Rat) / 10240000000), R := ((50068869313 : Rat) / 20480000000), D0 := ((50068869313 : Rat) / 20480000000), D1 := ((2569395853 : Rat) / 4096000000), D2 := ((1162522043 : Rat) / 10240000000), D3 := ((10289032609514508983 : Rat) / 50000000000000000000), D4 := ((1055428829389299353 : Rat) / 3125000000000000000), LB := ((1509665323246867 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50068869313 : Rat) / 20480000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((2317639487 : Rat) / 20480000000), D3 := ((10270954975237165233 : Rat) / 50000000000000000000), D4 := ((8434391817975722949 : Rat) / 25000000000000000000), LB := ((5794713155524989 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((50083678511 : Rat) / 20480000000), D0 := ((50083678511 : Rat) / 20480000000), D1 := ((12861788463 : Rat) / 20480000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10252877340959821483 : Rat) / 50000000000000000000), D4 := ((4212676500418525537 : Rat) / 12500000000000000000), LB := ((5564840007770133 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50083678511 : Rat) / 20480000000), R := ((5009108311 : Rat) / 2048000000), D0 := ((5009108311 : Rat) / 2048000000), D1 := ((6434596531 : Rat) / 10240000000), D2 := ((2302830289 : Rat) / 20480000000), D3 := ((10234799706682477733 : Rat) / 50000000000000000000), D4 := ((8416314183698379199 : Rat) / 25000000000000000000), LB := ((5349088003201441 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5009108311 : Rat) / 2048000000), R := ((50098487709 : Rat) / 20480000000), D0 := ((50098487709 : Rat) / 20480000000), D1 := ((12876597661 : Rat) / 20480000000), D2 := ((229542569 : Rat) / 2048000000), D3 := ((10216722072405133983 : Rat) / 50000000000000000000), D4 := ((2101818841639926831 : Rat) / 6250000000000000000), LB := ((5147503672293663 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50098487709 : Rat) / 20480000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((2288021091 : Rat) / 20480000000), D3 := ((10198644438127790233 : Rat) / 50000000000000000000), D4 := ((8398236549421035449 : Rat) / 25000000000000000000), LB := ((2480066963323063 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((50113296907 : Rat) / 20480000000), D0 := ((50113296907 : Rat) / 20480000000), D1 := ((12891406859 : Rat) / 20480000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((10180566803850446483 : Rat) / 50000000000000000000), D4 := ((4194598866141181787 : Rat) / 12500000000000000000), LB := ((4787026063133859 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50113296907 : Rat) / 20480000000), R := ((25060350753 : Rat) / 10240000000), D0 := ((25060350753 : Rat) / 10240000000), D1 := ((6449405729 : Rat) / 10240000000), D2 := ((2273211893 : Rat) / 20480000000), D3 := ((10162489169573102733 : Rat) / 50000000000000000000), D4 := ((8380158915143691699 : Rat) / 25000000000000000000), LB := ((925645553634169 : Rat) / 2000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25060350753 : Rat) / 10240000000), R := ((10025621221 : Rat) / 4096000000), D0 := ((10025621221 : Rat) / 4096000000), D1 := ((12906216057 : Rat) / 20480000000), D2 := ((1132903647 : Rat) / 10240000000), D3 := ((10144411535295758983 : Rat) / 50000000000000000000), D4 := ((523195006125313739 : Rat) / 1562500000000000000), LB := ((22418935609873347 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10025621221 : Rat) / 4096000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 4096000000), D3 := ((10126333901018415233 : Rat) / 50000000000000000000), D4 := ((8362081280866347949 : Rat) / 25000000000000000000), LB := ((1088438150739987 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((50142915303 : Rat) / 20480000000), D0 := ((50142915303 : Rat) / 20480000000), D1 := ((2584205051 : Rat) / 4096000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10108256266741071483 : Rat) / 50000000000000000000), D4 := ((4176521231863838037 : Rat) / 12500000000000000000), LB := ((847634618430293 : Rat) / 2000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50142915303 : Rat) / 20480000000), R := ((25075159951 : Rat) / 10240000000), D0 := ((25075159951 : Rat) / 10240000000), D1 := ((6464214927 : Rat) / 10240000000), D2 := ((2243593497 : Rat) / 20480000000), D3 := ((10090178632463727733 : Rat) / 50000000000000000000), D4 := ((8344003646589004199 : Rat) / 25000000000000000000), LB := ((4137097877684459 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25075159951 : Rat) / 10240000000), R := ((50157724501 : Rat) / 20480000000), D0 := ((50157724501 : Rat) / 20480000000), D1 := ((12935834453 : Rat) / 20480000000), D2 := ((1118094449 : Rat) / 10240000000), D3 := ((10072100998186383983 : Rat) / 50000000000000000000), D4 := ((2083741207362583081 : Rat) / 6250000000000000000), LB := ((40505766593734727 : Rat) / 100000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50157724501 : Rat) / 20480000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((2228784299 : Rat) / 20480000000), D3 := ((10054023363909040233 : Rat) / 50000000000000000000), D4 := ((8325926012311660449 : Rat) / 25000000000000000000), LB := ((1989329776669463 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((501651291 : Rat) / 204800000), R := ((50172533699 : Rat) / 20480000000), D0 := ((50172533699 : Rat) / 20480000000), D1 := ((12950643651 : Rat) / 20480000000), D2 := ((22213797 : Rat) / 204800000), D3 := ((10035945729631696483 : Rat) / 50000000000000000000), D4 := ((4158443597586494287 : Rat) / 12500000000000000000), LB := ((61271829635977 : Rat) / 156250000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50172533699 : Rat) / 20480000000), R := ((25089969149 : Rat) / 10240000000), D0 := ((25089969149 : Rat) / 10240000000), D1 := ((51832193 : Rat) / 81920000), D2 := ((2213975101 : Rat) / 20480000000), D3 := ((10017868095354352733 : Rat) / 50000000000000000000), D4 := ((8307848378034316699 : Rat) / 25000000000000000000), LB := ((1939420126206709 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25089969149 : Rat) / 10240000000), R := ((50187342897 : Rat) / 20480000000), D0 := ((50187342897 : Rat) / 20480000000), D1 := ((12965452849 : Rat) / 20480000000), D2 := ((1103285251 : Rat) / 10240000000), D3 := ((9999790461077008983 : Rat) / 50000000000000000000), D4 := ((1037351195111955603 : Rat) / 3125000000000000000), LB := ((3851040414021567 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50187342897 : Rat) / 20480000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((2199165903 : Rat) / 20480000000), D3 := ((9981712826799665233 : Rat) / 50000000000000000000), D4 := ((8289770743756972949 : Rat) / 25000000000000000000), LB := ((19190247053425813 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((10040430419 : Rat) / 4096000000), D0 := ((10040430419 : Rat) / 4096000000), D1 := ((12980262047 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((9963635192522321483 : Rat) / 50000000000000000000), D4 := ((4140365963309150537 : Rat) / 12500000000000000000), LB := ((7679839024224977 : Rat) / 20000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10040430419 : Rat) / 4096000000), R := ((25104778347 : Rat) / 10240000000), D0 := ((25104778347 : Rat) / 10240000000), D1 := ((6493833323 : Rat) / 10240000000), D2 := ((436871341 : Rat) / 4096000000), D3 := ((9945557558244977733 : Rat) / 50000000000000000000), D4 := ((8271693109479629199 : Rat) / 25000000000000000000), LB := ((2410439646051421 : Rat) / 6250000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25104778347 : Rat) / 10240000000), R := ((50216961293 : Rat) / 20480000000), D0 := ((50216961293 : Rat) / 20480000000), D1 := ((2599014249 : Rat) / 4096000000), D2 := ((1088476053 : Rat) / 10240000000), D3 := ((9927479923967633983 : Rat) / 50000000000000000000), D4 := ((2065663573085239331 : Rat) / 6250000000000000000), LB := ((38884543415751427 : Rat) / 100000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50216961293 : Rat) / 20480000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((2169547507 : Rat) / 20480000000), D3 := ((9909402289690290233 : Rat) / 50000000000000000000), D4 := ((8253615475202285449 : Rat) / 25000000000000000000), LB := ((3935225858041347 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((50231770491 : Rat) / 20480000000), D0 := ((50231770491 : Rat) / 20480000000), D1 := ((13009880443 : Rat) / 20480000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((9891324655412946483 : Rat) / 50000000000000000000), D4 := ((4122288329031806787 : Rat) / 12500000000000000000), LB := ((1998536033350623 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50231770491 : Rat) / 20480000000), R := ((5023917509 : Rat) / 2048000000), D0 := ((5023917509 : Rat) / 2048000000), D1 := ((6508642521 : Rat) / 10240000000), D2 := ((2154738309 : Rat) / 20480000000), D3 := ((9873247021135602733 : Rat) / 50000000000000000000), D4 := ((8235537840924941699 : Rat) / 25000000000000000000), LB := ((4074047517984569 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5023917509 : Rat) / 2048000000), R := ((50246579689 : Rat) / 20480000000), D0 := ((50246579689 : Rat) / 20480000000), D1 := ((13024689641 : Rat) / 20480000000), D2 := ((214733371 : Rat) / 2048000000), D3 := ((9855169386858258983 : Rat) / 50000000000000000000), D4 := ((64269523623330233 : Rat) / 195312500000000000), LB := ((41662072345963197 : Rat) / 100000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50246579689 : Rat) / 20480000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((2139929111 : Rat) / 20480000000), D3 := ((9837091752580915233 : Rat) / 50000000000000000000), D4 := ((8217460206647597949 : Rat) / 25000000000000000000), LB := ((2136803358555317 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((50261388887 : Rat) / 20480000000), D0 := ((50261388887 : Rat) / 20480000000), D1 := ((13039498839 : Rat) / 20480000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9819014118303571483 : Rat) / 50000000000000000000), D4 := ((4104210694754463037 : Rat) / 12500000000000000000), LB := ((21981509748320027 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50261388887 : Rat) / 20480000000), R := ((25134396743 : Rat) / 10240000000), D0 := ((25134396743 : Rat) / 10240000000), D1 := ((6523451719 : Rat) / 10240000000), D2 := ((2125119913 : Rat) / 20480000000), D3 := ((9800936484026227733 : Rat) / 50000000000000000000), D4 := ((8199382572370254199 : Rat) / 25000000000000000000), LB := ((22671747028331357 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25134396743 : Rat) / 10240000000), R := ((10055239617 : Rat) / 4096000000), D0 := ((10055239617 : Rat) / 4096000000), D1 := ((13054308037 : Rat) / 20480000000), D2 := ((1058857657 : Rat) / 10240000000), D3 := ((9782858849748883983 : Rat) / 50000000000000000000), D4 := ((2047585938807895581 : Rat) / 6250000000000000000), LB := ((46878060537158817 : Rat) / 100000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((10055239617 : Rat) / 4096000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((422062143 : Rat) / 4096000000), D3 := ((9764781215471540233 : Rat) / 50000000000000000000), D4 := ((8181304938092910449 : Rat) / 25000000000000000000), LB := ((97134587270431 : Rat) / 200000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((50291007283 : Rat) / 20480000000), D0 := ((50291007283 : Rat) / 20480000000), D1 := ((2613823447 : Rat) / 4096000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((9746703581194196483 : Rat) / 50000000000000000000), D4 := ((4086133060477119287 : Rat) / 12500000000000000000), LB := ((2520588655975653 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50291007283 : Rat) / 20480000000), R := ((25149205941 : Rat) / 10240000000), D0 := ((25149205941 : Rat) / 10240000000), D1 := ((6538260917 : Rat) / 10240000000), D2 := ((2095501517 : Rat) / 20480000000), D3 := ((9728625946916852733 : Rat) / 50000000000000000000), D4 := ((8163227303815566699 : Rat) / 25000000000000000000), LB := ((163787762162311 : Rat) / 312500000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25149205941 : Rat) / 10240000000), R := ((50305816481 : Rat) / 20480000000), D0 := ((50305816481 : Rat) / 20480000000), D1 := ((13083926433 : Rat) / 20480000000), D2 := ((1044048459 : Rat) / 10240000000), D3 := ((9710548312639508983 : Rat) / 50000000000000000000), D4 := ((1019273560834611853 : Rat) / 3125000000000000000), LB := ((5456881604981589 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50305816481 : Rat) / 20480000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((2080692319 : Rat) / 20480000000), D3 := ((9692470678362165233 : Rat) / 50000000000000000000), D4 := ((8145149669538222949 : Rat) / 25000000000000000000), LB := ((5688256494977839 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((50320625679 : Rat) / 20480000000), D0 := ((50320625679 : Rat) / 20480000000), D1 := ((13098735631 : Rat) / 20480000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9674393044084821483 : Rat) / 50000000000000000000), D4 := ((4068055426199775537 : Rat) / 12500000000000000000), LB := ((5935393127200483 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50320625679 : Rat) / 20480000000), R := ((25164015139 : Rat) / 10240000000), D0 := ((25164015139 : Rat) / 10240000000), D1 := ((1310614023 : Rat) / 2048000000), D2 := ((2065883121 : Rat) / 20480000000), D3 := ((9656315409807477733 : Rat) / 50000000000000000000), D4 := ((8127072035260879199 : Rat) / 25000000000000000000), LB := ((1549588027152729 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25164015139 : Rat) / 10240000000), R := ((12585709869 : Rat) / 5120000000), D0 := ((12585709869 : Rat) / 5120000000), D1 := ((3280237357 : Rat) / 5120000000), D2 := ((1029239261 : Rat) / 10240000000), D3 := ((9638237775530133983 : Rat) / 50000000000000000000), D4 := ((2029508304530551831 : Rat) / 6250000000000000000), LB := ((90369056627293 : Rat) / 2000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12585709869 : Rat) / 5120000000), R := ((25178824337 : Rat) / 10240000000), D0 := ((25178824337 : Rat) / 10240000000), D1 := ((6567879313 : Rat) / 10240000000), D2 := ((510917331 : Rat) / 5120000000), D3 := ((9602082506975446483 : Rat) / 50000000000000000000), D4 := ((4049977791922431787 : Rat) / 12500000000000000000), LB := ((5314984036396131 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25178824337 : Rat) / 10240000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((1014430063 : Rat) / 10240000000), D3 := ((9565927238420758983 : Rat) / 50000000000000000000), D4 := ((505117371847969989 : Rat) / 1562500000000000000), LB := ((8692091426858173 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((5038726707 : Rat) / 2048000000), D0 := ((5038726707 : Rat) / 2048000000), D1 := ((6582688511 : Rat) / 10240000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9529771969866071483 : Rat) / 50000000000000000000), D4 := ((4031900157645088037 : Rat) / 12500000000000000000), LB := ((2478619325937681 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((5038726707 : Rat) / 2048000000), R := ((12600519067 : Rat) / 5120000000), D0 := ((12600519067 : Rat) / 5120000000), D1 := ((659009311 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 2048000000), D3 := ((9493616701311383983 : Rat) / 50000000000000000000), D4 := ((2011430670253208081 : Rat) / 6250000000000000000), LB := ((16420594737441563 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12600519067 : Rat) / 5120000000), R := ((25208442733 : Rat) / 10240000000), D0 := ((25208442733 : Rat) / 10240000000), D1 := ((6597497709 : Rat) / 10240000000), D2 := ((496108133 : Rat) / 5120000000), D3 := ((9457461432756696483 : Rat) / 50000000000000000000), D4 := ((4013822523367744287 : Rat) / 12500000000000000000), LB := ((2077722910428237 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25208442733 : Rat) / 10240000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((984811667 : Rat) / 10240000000), D3 := ((9421306164202008983 : Rat) / 50000000000000000000), D4 := ((1001195926557268103 : Rat) / 3125000000000000000), LB := ((2546569259961051 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((25223251931 : Rat) / 10240000000), D0 := ((25223251931 : Rat) / 10240000000), D1 := ((6612306907 : Rat) / 10240000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9385150895647321483 : Rat) / 50000000000000000000), D4 := ((3995744889090400537 : Rat) / 12500000000000000000), LB := ((30488728906021 : Rat) / 50000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25223251931 : Rat) / 10240000000), R := ((2523065653 : Rat) / 1024000000), D0 := ((2523065653 : Rat) / 1024000000), D1 := ((3309855753 : Rat) / 5120000000), D2 := ((970002469 : Rat) / 10240000000), D3 := ((9348995627092633983 : Rat) / 50000000000000000000), D4 := ((1993353035975864331 : Rat) / 6250000000000000000), LB := ((7169826772645549 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2523065653 : Rat) / 1024000000), R := ((25238061129 : Rat) / 10240000000), D0 := ((25238061129 : Rat) / 10240000000), D1 := ((1325423221 : Rat) / 2048000000), D2 := ((96259787 : Rat) / 1024000000), D3 := ((9312840358537946483 : Rat) / 50000000000000000000), D4 := ((3977667254813056787 : Rat) / 12500000000000000000), LB := ((2077487843010553 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25238061129 : Rat) / 10240000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((955193271 : Rat) / 10240000000), D3 := ((9276685089983258983 : Rat) / 50000000000000000000), D4 := ((248039277354649057 : Rat) / 781250000000000000), LB := ((2379675113859253 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((197230201 : Rat) / 80000000), R := ((25252870327 : Rat) / 10240000000), D0 := ((25252870327 : Rat) / 10240000000), D1 := ((6641925303 : Rat) / 10240000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9240529821428571483 : Rat) / 50000000000000000000), D4 := ((3959589620535713037 : Rat) / 12500000000000000000), LB := ((2159333239226957 : Rat) / 2000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((25252870327 : Rat) / 10240000000), R := ((12630137463 : Rat) / 5120000000), D0 := ((12630137463 : Rat) / 5120000000), D1 := ((3324664951 : Rat) / 5120000000), D2 := ((940384073 : Rat) / 10240000000), D3 := ((9204374552873883983 : Rat) / 50000000000000000000), D4 := ((1975275401698520581 : Rat) / 6250000000000000000), LB := ((6072226187307239 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12630137463 : Rat) / 5120000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((466489737 : Rat) / 5120000000), D3 := ((9168219284319196483 : Rat) / 50000000000000000000), D4 := ((3941511986258369287 : Rat) / 12500000000000000000), LB := ((3326134829388927 : Rat) / 20000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((12644946661 : Rat) / 5120000000), D0 := ((12644946661 : Rat) / 5120000000), D1 := ((3339474149 : Rat) / 5120000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9095908747209821483 : Rat) / 50000000000000000000), D4 := ((3923434351981025537 : Rat) / 12500000000000000000), LB := ((4734960236672803 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12644946661 : Rat) / 5120000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 5120000000), D3 := ((9023598210100446483 : Rat) / 50000000000000000000), D4 := ((3905356717703681787 : Rat) / 12500000000000000000), LB := ((8096209263667997 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((632617563 : Rat) / 256000000), R := ((12659755859 : Rat) / 5120000000), D0 := ((12659755859 : Rat) / 5120000000), D1 := ((3354283347 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((8951287672991071483 : Rat) / 50000000000000000000), D4 := ((3887279083426338037 : Rat) / 12500000000000000000), LB := ((91814108379943 : Rat) / 78125000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12659755859 : Rat) / 5120000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((436871341 : Rat) / 5120000000), D3 := ((8878977135881696483 : Rat) / 50000000000000000000), D4 := ((3869201449148994287 : Rat) / 12500000000000000000), LB := ((49089273882039 : Rat) / 31250000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((12674565057 : Rat) / 5120000000), D0 := ((12674565057 : Rat) / 5120000000), D1 := ((673818509 : Rat) / 1024000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((8806666598772321483 : Rat) / 50000000000000000000), D4 := ((3851123814871650537 : Rat) / 12500000000000000000), LB := ((499278800537073 : Rat) / 250000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((12674565057 : Rat) / 5120000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((422062143 : Rat) / 5120000000), D3 := ((8734356061662946483 : Rat) / 50000000000000000000), D4 := ((3833046180594306787 : Rat) / 12500000000000000000), LB := ((6136517779924619 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8662045524553571483 : Rat) / 50000000000000000000), D4 := ((3814968546316963037 : Rat) / 12500000000000000000), LB := ((1492717128583551 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((8517424450334821483 : Rat) / 50000000000000000000), D4 := ((3778813277762275537 : Rat) / 12500000000000000000), LB := ((8412420776869739 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8372803376116071483 : Rat) / 50000000000000000000), D4 := ((3742658009207588037 : Rat) / 12500000000000000000), LB := ((14518585201167833 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8228182301897321483 : Rat) / 50000000000000000000), D4 := ((3706502740652900537 : Rat) / 12500000000000000000), LB := ((4267065735686887 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8083561227678571483 : Rat) / 50000000000000000000), D4 := ((3670347472098213037 : Rat) / 12500000000000000000), LB := ((5819313172695101 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((7794319079241071483 : Rat) / 50000000000000000000), D4 := ((3598036934988838037 : Rat) / 12500000000000000000), LB := ((2349665494701683 : Rat) / 500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7505076930803571483 : Rat) / 50000000000000000000), D4 := ((3525726397879463037 : Rat) / 12500000000000000000), LB := ((2233658726990849 : Rat) / 250000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7215834782366071483 : Rat) / 50000000000000000000), D4 := ((3453415860770088037 : Rat) / 12500000000000000000), LB := ((13961913011347443 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6926592633928571483 : Rat) / 50000000000000000000), D4 := ((3381105323660713037 : Rat) / 12500000000000000000), LB := ((10965582399127677 : Rat) / 1000000000000000000) }
]

def block390RightChunk000L : Rat := ((87051899553571428739 : Rat) / 50000000000000000000)
def block390RightChunk000R : Rat := ((1614864603 : Rat) / 640000000)

def block390RightChunk000Certificate : Bool :=
  allBoxesValid block390RightChunk000 &&
  coversFromBool block390RightChunk000 block390RightChunk000L block390RightChunk000R

theorem block390RightChunk000Certificate_eq_true :
    block390RightChunk000Certificate = true := by
  native_decide

def block390RightChunk001 : List RatBox := [
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6348108337053571483 : Rat) / 50000000000000000000), D4 := ((3236484249441963037 : Rat) / 12500000000000000000), LB := ((26415052053292337 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5769624040178571483 : Rat) / 50000000000000000000), D4 := ((3091863175223213037 : Rat) / 12500000000000000000), LB := ((392826363396219 : Rat) / 12500000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((511587 : Rat) / 200000), R := ((516199655446428571483 : Rat) / 200000000000000000000), D0 := ((516199655446428571483 : Rat) / 200000000000000000000), D1 := ((152704635446428571483 : Rat) / 200000000000000000000), D2 := ((4612655446428571483 : Rat) / 200000000000000000000), D3 := ((4612655446428571483 : Rat) / 50000000000000000000), D4 := ((2802621026785713037 : Rat) / 12500000000000000000), LB := ((3152911074162771 : Rat) / 62500000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((516199655446428571483 : Rat) / 200000000000000000000), R := ((260406155446428571483 : Rat) / 100000000000000000000), D0 := ((260406155446428571483 : Rat) / 100000000000000000000), D1 := ((78658645446428571483 : Rat) / 100000000000000000000), D2 := ((4612655446428571483 : Rat) / 100000000000000000000), D3 := ((13837966339285714449 : Rat) / 200000000000000000000), D4 := ((40229280982142837109 : Rat) / 200000000000000000000), LB := ((27015098280496433 : Rat) / 500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((260406155446428571483 : Rat) / 100000000000000000000), R := ((132509405446428571483 : Rat) / 50000000000000000000), D0 := ((132509405446428571483 : Rat) / 50000000000000000000), D1 := ((41635650446428571483 : Rat) / 50000000000000000000), D2 := ((4612655446428571483 : Rat) / 50000000000000000000), D3 := ((4612655446428571483 : Rat) / 100000000000000000000), D4 := ((17808312767857132813 : Rat) / 100000000000000000000), LB := ((306674411948649 : Rat) / 6250000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((132509405446428571483 : Rat) / 50000000000000000000), R := ((269571079553571428793 : Rat) / 100000000000000000000), D0 := ((269571079553571428793 : Rat) / 100000000000000000000), D1 := ((87823569553571428793 : Rat) / 100000000000000000000), D2 := ((13777579553571428793 : Rat) / 100000000000000000000), D3 := ((4552268660714285827 : Rat) / 100000000000000000000), D4 := ((1319565732142856133 : Rat) / 10000000000000000000), LB := ((18499048818603203 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((269571079553571428793 : Rat) / 100000000000000000000), R := ((1082836586875000000999 : Rat) / 400000000000000000000), D0 := ((1082836586875000000999 : Rat) / 400000000000000000000), D1 := ((355846546875000000999 : Rat) / 400000000000000000000), D2 := ((59662586875000000999 : Rat) / 400000000000000000000), D3 := ((4552268660714285827 : Rat) / 80000000000000000000), D4 := ((8643388660714275503 : Rat) / 100000000000000000000), LB := ((602053079228837 : Rat) / 25000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1082836586875000000999 : Rat) / 400000000000000000000), R := ((86809017696428571513 : Rat) / 32000000000000000000), D0 := ((86809017696428571513 : Rat) / 32000000000000000000), D1 := ((28649814496428571513 : Rat) / 32000000000000000000), D2 := ((4955097696428571513 : Rat) / 32000000000000000000), D3 := ((50074955267857144097 : Rat) / 800000000000000000000), D4 := ((6004257196428563237 : Rat) / 80000000000000000000), LB := ((977706936581263 : Rat) / 50000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((86809017696428571513 : Rat) / 32000000000000000000), R := ((543694427767857143413 : Rat) / 200000000000000000000), D0 := ((543694427767857143413 : Rat) / 200000000000000000000), D1 := ((180199407767857143413 : Rat) / 200000000000000000000), D2 := ((32107427767857143413 : Rat) / 200000000000000000000), D3 := ((13656805982142857481 : Rat) / 200000000000000000000), D4 := ((55490303303571346543 : Rat) / 800000000000000000000), LB := ((3728665748340493 : Rat) / 500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((543694427767857143413 : Rat) / 200000000000000000000), R := ((4354107690803571433131 : Rat) / 1600000000000000000000), D0 := ((4354107690803571433131 : Rat) / 1600000000000000000000), D1 := ((1446147530803571433131 : Rat) / 1600000000000000000000), D2 := ((261411690803571433131 : Rat) / 1600000000000000000000), D3 := ((4552268660714285827 : Rat) / 64000000000000000000), D4 := ((12734508660714265179 : Rat) / 200000000000000000000), LB := ((8628702955238321 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4354107690803571433131 : Rat) / 1600000000000000000000), R := ((2179329979732142859479 : Rat) / 800000000000000000000), D0 := ((2179329979732142859479 : Rat) / 800000000000000000000), D1 := ((725349899732142859479 : Rat) / 800000000000000000000), D2 := ((132981979732142859479 : Rat) / 800000000000000000000), D3 := ((59179492589285715751 : Rat) / 800000000000000000000), D4 := ((19464760124999967121 : Rat) / 320000000000000000000), LB := ((4285000586551013 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2179329979732142859479 : Rat) / 800000000000000000000), R := ((872642445625000000957 : Rat) / 320000000000000000000), D0 := ((872642445625000000957 : Rat) / 320000000000000000000), D1 := ((291050413625000000957 : Rat) / 320000000000000000000), D2 := ((54103245625000000957 : Rat) / 320000000000000000000), D3 := ((122911253839285717329 : Rat) / 1600000000000000000000), D4 := ((46385765982142774889 : Rat) / 800000000000000000000), LB := ((334263958241543 : Rat) / 625000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((872642445625000000957 : Rat) / 320000000000000000000), R := ((8730976724910714295397 : Rat) / 3200000000000000000000), D0 := ((8730976724910714295397 : Rat) / 3200000000000000000000), D1 := ((2915056404910714295397 : Rat) / 3200000000000000000000), D2 := ((545584724910714295397 : Rat) / 3200000000000000000000), D3 := ((50074955267857144097 : Rat) / 640000000000000000000), D4 := ((88219263303571263951 : Rat) / 1600000000000000000000), LB := ((2597329271234683 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8730976724910714295397 : Rat) / 3200000000000000000000), R := ((1091941124196428572653 : Rat) / 400000000000000000000), D0 := ((1091941124196428572653 : Rat) / 400000000000000000000), D1 := ((364951084196428572653 : Rat) / 400000000000000000000), D2 := ((68767124196428572653 : Rat) / 400000000000000000000), D3 := ((31865880625000000789 : Rat) / 400000000000000000000), D4 := ((6875450317857129683 : Rat) / 128000000000000000000), LB := ((2998935074424447 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1091941124196428572653 : Rat) / 400000000000000000000), R := ((699024410232142857931 : Rat) / 256000000000000000000), D0 := ((699024410232142857931 : Rat) / 256000000000000000000), D1 := ((233750784632142857931 : Rat) / 256000000000000000000), D2 := ((44193050232142857931 : Rat) / 256000000000000000000), D3 := ((514406358660714298451 : Rat) / 6400000000000000000000), D4 := ((20916748660714244531 : Rat) / 400000000000000000000), LB := ((12647441616190913 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((699024410232142857931 : Rat) / 256000000000000000000), R := ((8740081262232142867051 : Rat) / 3200000000000000000000), D0 := ((8740081262232142867051 : Rat) / 3200000000000000000000), D1 := ((2924160942232142867051 : Rat) / 3200000000000000000000), D2 := ((554689262232142867051 : Rat) / 3200000000000000000000), D3 := ((259479313660714292139 : Rat) / 3200000000000000000000), D4 := ((330115709910713626669 : Rat) / 6400000000000000000000), LB := ((1958943630065657 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8740081262232142867051 : Rat) / 3200000000000000000000), R := ((17484714793125000019929 : Rat) / 6400000000000000000000), D0 := ((17484714793125000019929 : Rat) / 6400000000000000000000), D1 := ((5852874153125000019929 : Rat) / 6400000000000000000000), D2 := ((1113930793125000019929 : Rat) / 6400000000000000000000), D3 := ((104702179196428574021 : Rat) / 1280000000000000000000), D4 := ((162781720624999670421 : Rat) / 3200000000000000000000), LB := ((3576309447627657 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17484714793125000019929 : Rat) / 6400000000000000000000), R := ((4372316765446428576439 : Rat) / 1600000000000000000000), D0 := ((4372316765446428576439 : Rat) / 1600000000000000000000), D1 := ((1464356605446428576439 : Rat) / 1600000000000000000000), D2 := ((279620765446428576439 : Rat) / 1600000000000000000000), D3 := ((132015791160714288983 : Rat) / 1600000000000000000000), D4 := ((64202234517857011003 : Rat) / 1280000000000000000000), LB := ((9447746163462889 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4372316765446428576439 : Rat) / 1600000000000000000000), R := ((17493819330446428591583 : Rat) / 6400000000000000000000), D0 := ((17493819330446428591583 : Rat) / 6400000000000000000000), D1 := ((5861978690446428591583 : Rat) / 6400000000000000000000), D2 := ((1123035330446428591583 : Rat) / 6400000000000000000000), D3 := ((532615433303571441759 : Rat) / 6400000000000000000000), D4 := ((79114725982142692297 : Rat) / 1600000000000000000000), LB := ((5022813673175031 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17493819330446428591583 : Rat) / 6400000000000000000000), R := ((1749837159910714287741 : Rat) / 640000000000000000000), D0 := ((1749837159910714287741 : Rat) / 640000000000000000000), D1 := ((586653095910714287741 : Rat) / 640000000000000000000), D2 := ((112758759910714287741 : Rat) / 640000000000000000000), D3 := ((268583850982142863793 : Rat) / 3200000000000000000000), D4 := ((311906635267856483361 : Rat) / 6400000000000000000000), LB := ((5183518678975041 : Rat) / 50000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1749837159910714287741 : Rat) / 640000000000000000000), R := ((35001295466875000040647 : Rat) / 12800000000000000000000), D0 := ((35001295466875000040647 : Rat) / 12800000000000000000000), D1 := ((11737614186875000040647 : Rat) / 12800000000000000000000), D2 := ((2259727466875000040647 : Rat) / 12800000000000000000000), D3 := ((1078887672589285740999 : Rat) / 12800000000000000000000), D4 := ((153677183303571098767 : Rat) / 3200000000000000000000), LB := ((9959411242349003 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35001295466875000040647 : Rat) / 12800000000000000000000), R := ((17502923867767857163237 : Rat) / 6400000000000000000000), D0 := ((17502923867767857163237 : Rat) / 6400000000000000000000), D1 := ((5871083227767857163237 : Rat) / 6400000000000000000000), D2 := ((1132139867767857163237 : Rat) / 6400000000000000000000), D3 := ((541719970625000013413 : Rat) / 6400000000000000000000), D4 := ((610156464553570109241 : Rat) / 12800000000000000000000), LB := ((8325139486304867 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17502923867767857163237 : Rat) / 6400000000000000000000), R := ((35010400004196428612301 : Rat) / 12800000000000000000000), D0 := ((35010400004196428612301 : Rat) / 12800000000000000000000), D1 := ((11746718724196428612301 : Rat) / 12800000000000000000000), D2 := ((2268832004196428612301 : Rat) / 12800000000000000000000), D3 := ((1087992209910714312653 : Rat) / 12800000000000000000000), D4 := ((302802097946427911707 : Rat) / 6400000000000000000000), LB := ((68052220722703 : Rat) / 100000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35010400004196428612301 : Rat) / 12800000000000000000000), R := ((2188434517053571431133 : Rat) / 800000000000000000000), D0 := ((2188434517053571431133 : Rat) / 800000000000000000000), D1 := ((734454437053571431133 : Rat) / 800000000000000000000), D2 := ((142086517053571431133 : Rat) / 800000000000000000000), D3 := ((13656805982142857481 : Rat) / 160000000000000000000), D4 := ((601051927232141537587 : Rat) / 12800000000000000000000), LB := ((540062286800369 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((2188434517053571431133 : Rat) / 800000000000000000000), R := ((7003900908303571436791 : Rat) / 2560000000000000000000), D0 := ((7003900908303571436791 : Rat) / 2560000000000000000000), D1 := ((2351164652303571436791 : Rat) / 2560000000000000000000), D2 := ((455587308303571436791 : Rat) / 2560000000000000000000), D3 := ((1097096747232142884307 : Rat) / 12800000000000000000000), D4 := ((7456245732142840647 : Rat) / 160000000000000000000), LB := ((4112336842452269 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((7003900908303571436791 : Rat) / 2560000000000000000000), R := ((17512028405089285734891 : Rat) / 6400000000000000000000), D0 := ((17512028405089285734891 : Rat) / 6400000000000000000000), D1 := ((5880187765089285734891 : Rat) / 6400000000000000000000), D2 := ((1141244405089285734891 : Rat) / 6400000000000000000000), D3 := ((550824507946428585067 : Rat) / 6400000000000000000000), D4 := ((591947389910712965933 : Rat) / 12800000000000000000000), LB := ((1838369292931491 : Rat) / 6250000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17512028405089285734891 : Rat) / 6400000000000000000000), R := ((35028609078839285755609 : Rat) / 12800000000000000000000), D0 := ((35028609078839285755609 : Rat) / 12800000000000000000000), D1 := ((11764927798839285755609 : Rat) / 12800000000000000000000), D2 := ((2287041078839285755609 : Rat) / 12800000000000000000000), D3 := ((1106201284553571455961 : Rat) / 12800000000000000000000), D4 := ((293697560624999340053 : Rat) / 6400000000000000000000), LB := ((3777689121926553 : Rat) / 20000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35028609078839285755609 : Rat) / 12800000000000000000000), R := ((8758290336875000010359 : Rat) / 3200000000000000000000), D0 := ((8758290336875000010359 : Rat) / 3200000000000000000000), D1 := ((2942370016875000010359 : Rat) / 3200000000000000000000), D2 := ((572898336875000010359 : Rat) / 3200000000000000000000), D3 := ((277688388303571435447 : Rat) / 3200000000000000000000), D4 := ((582842852589284394279 : Rat) / 12800000000000000000000), LB := ((74671183379919 : Rat) / 781250000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8758290336875000010359 : Rat) / 3200000000000000000000), R := ((35037713616160714327263 : Rat) / 12800000000000000000000), D0 := ((35037713616160714327263 : Rat) / 12800000000000000000000), D1 := ((11774032336160714327263 : Rat) / 12800000000000000000000), D2 := ((2296145616160714327263 : Rat) / 12800000000000000000000), D3 := ((223061164375000005523 : Rat) / 2560000000000000000000), D4 := ((144572645982142527113 : Rat) / 3200000000000000000000), LB := ((2867167585451913 : Rat) / 200000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35037713616160714327263 : Rat) / 12800000000000000000000), R := ((70079979500982142940353 : Rat) / 25600000000000000000000), D0 := ((70079979500982142940353 : Rat) / 25600000000000000000000), D1 := ((23552616940982142940353 : Rat) / 25600000000000000000000), D2 := ((4596843500982142940353 : Rat) / 25600000000000000000000), D3 := ((2235163912410714341057 : Rat) / 25600000000000000000000), D4 := ((4589906522142846581 : Rat) / 102400000000000000000), LB := ((5550958592216437 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70079979500982142940353 : Rat) / 25600000000000000000000), R := ((3504226588482142861309 : Rat) / 1280000000000000000000), D0 := ((3504226588482142861309 : Rat) / 1280000000000000000000), D1 := ((1177858460482142861309 : Rat) / 1280000000000000000000), D2 := ((230069788482142861309 : Rat) / 1280000000000000000000), D3 := ((559929045267857156721 : Rat) / 6400000000000000000000), D4 := ((1142924361874997359423 : Rat) / 25600000000000000000000), LB := ((5243860469482109 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((3504226588482142861309 : Rat) / 1280000000000000000000), R := ((70089084038303571512007 : Rat) / 25600000000000000000000), D0 := ((70089084038303571512007 : Rat) / 25600000000000000000000), D1 := ((23561721478303571512007 : Rat) / 25600000000000000000000), D2 := ((4605948038303571512007 : Rat) / 25600000000000000000000), D3 := ((2244268449732142912711 : Rat) / 25600000000000000000000), D4 := ((284593023303570768399 : Rat) / 6400000000000000000000), LB := ((2483845334691759 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70089084038303571512007 : Rat) / 25600000000000000000000), R := ((35046818153482142898917 : Rat) / 12800000000000000000000), D0 := ((35046818153482142898917 : Rat) / 12800000000000000000000), D1 := ((11783136873482142898917 : Rat) / 12800000000000000000000), D2 := ((2305250153482142898917 : Rat) / 12800000000000000000000), D3 := ((1124410359196428599269 : Rat) / 12800000000000000000000), D4 := ((1133819824553568787769 : Rat) / 25600000000000000000000), LB := ((2361302421429179 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35046818153482142898917 : Rat) / 12800000000000000000000), R := ((70098188575625000083661 : Rat) / 25600000000000000000000), D0 := ((70098188575625000083661 : Rat) / 25600000000000000000000), D1 := ((23570826015625000083661 : Rat) / 25600000000000000000000), D2 := ((4615052575625000083661 : Rat) / 25600000000000000000000), D3 := ((450674597410714296873 : Rat) / 5120000000000000000000), D4 := ((564633777946427250971 : Rat) / 12800000000000000000000), LB := ((450876105258291 : Rat) / 1000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70098188575625000083661 : Rat) / 25600000000000000000000), R := ((4381421302767857148093 : Rat) / 1600000000000000000000), D0 := ((4381421302767857148093 : Rat) / 1600000000000000000000), D1 := ((1473461142767857148093 : Rat) / 1600000000000000000000), D2 := ((288725302767857148093 : Rat) / 1600000000000000000000), D3 := ((141120328482142860637 : Rat) / 1600000000000000000000), D4 := ((224943057446428043223 : Rat) / 5120000000000000000000), LB := ((2163159903810219 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((4381421302767857148093 : Rat) / 1600000000000000000000), R := ((14021458622589285731063 : Rat) / 5120000000000000000000), D0 := ((14021458622589285731063 : Rat) / 5120000000000000000000), D1 := ((4715986110589285731063 : Rat) / 5120000000000000000000), D2 := ((924831422589285731063 : Rat) / 5120000000000000000000), D3 := ((2262477524375000056019 : Rat) / 25600000000000000000000), D4 := ((70010188660714120643 : Rat) / 1600000000000000000000), LB := ((1043861024726811 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((14021458622589285731063 : Rat) / 5120000000000000000000), R := ((35055922690803571470571 : Rat) / 12800000000000000000000), D0 := ((35055922690803571470571 : Rat) / 12800000000000000000000), D1 := ((11792241410803571470571 : Rat) / 12800000000000000000000), D2 := ((2314354690803571470571 : Rat) / 12800000000000000000000), D3 := ((1133514896517857170923 : Rat) / 12800000000000000000000), D4 := ((1115610749910711644461 : Rat) / 25600000000000000000000), LB := ((4056299435428179 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35055922690803571470571 : Rat) / 12800000000000000000000), R := ((70116397650267857226969 : Rat) / 25600000000000000000000), D0 := ((70116397650267857226969 : Rat) / 25600000000000000000000), D1 := ((23589035090267857226969 : Rat) / 25600000000000000000000), D2 := ((4633261650267857226969 : Rat) / 25600000000000000000000), D3 := ((2271582061696428627673 : Rat) / 25600000000000000000000), D4 := ((555529240624998679317 : Rat) / 12800000000000000000000), LB := ((9922634703235511 : Rat) / 25000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70116397650267857226969 : Rat) / 25600000000000000000000), R := ((17530237479732142878199 : Rat) / 6400000000000000000000), D0 := ((17530237479732142878199 : Rat) / 6400000000000000000000), D1 := ((5898396839732142878199 : Rat) / 6400000000000000000000), D2 := ((1159453479732142878199 : Rat) / 6400000000000000000000), D3 := ((4552268660714285827 : Rat) / 51200000000000000000), D4 := ((1106506212589283072807 : Rat) / 25600000000000000000000), LB := ((782775618688003 : Rat) / 2000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17530237479732142878199 : Rat) / 6400000000000000000000), R := ((70125502187589285798623 : Rat) / 25600000000000000000000), D0 := ((70125502187589285798623 : Rat) / 25600000000000000000000), D1 := ((23598139627589285798623 : Rat) / 25600000000000000000000), D2 := ((4642366187589285798623 : Rat) / 25600000000000000000000), D3 := ((2280686599017857199327 : Rat) / 25600000000000000000000), D4 := ((55097697196428439349 : Rat) / 1280000000000000000000), LB := ((1215920425105127 : Rat) / 3125000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70125502187589285798623 : Rat) / 25600000000000000000000), R := ((1402601089125000001689 : Rat) / 512000000000000000000), D0 := ((1402601089125000001689 : Rat) / 512000000000000000000), D1 := ((472053837925000001689 : Rat) / 512000000000000000000), D2 := ((92938369125000001689 : Rat) / 512000000000000000000), D3 := ((1142619433839285742577 : Rat) / 12800000000000000000000), D4 := ((1097401675267854501153 : Rat) / 25600000000000000000000), LB := ((975107910351769 : Rat) / 2500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((1402601089125000001689 : Rat) / 512000000000000000000), R := ((70134606724910714370277 : Rat) / 25600000000000000000000), D0 := ((70134606724910714370277 : Rat) / 25600000000000000000000), D1 := ((23607244164910714370277 : Rat) / 25600000000000000000000), D2 := ((4651470724910714370277 : Rat) / 25600000000000000000000), D3 := ((2289791136339285770981 : Rat) / 25600000000000000000000), D4 := ((546424703303570107663 : Rat) / 12800000000000000000000), LB := ((3942515607374131 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70134606724910714370277 : Rat) / 25600000000000000000000), R := ((8767394874196428582013 : Rat) / 3200000000000000000000), D0 := ((8767394874196428582013 : Rat) / 3200000000000000000000), D1 := ((2951474554196428582013 : Rat) / 3200000000000000000000), D2 := ((582002874196428582013 : Rat) / 3200000000000000000000), D3 := ((286792925625000007101 : Rat) / 3200000000000000000000), D4 := ((1088297137946425929499 : Rat) / 25600000000000000000000), LB := ((4017378681433481 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((8767394874196428582013 : Rat) / 3200000000000000000000), R := ((70143711262232142941931 : Rat) / 25600000000000000000000), D0 := ((70143711262232142941931 : Rat) / 25600000000000000000000), D1 := ((23616348702232142941931 : Rat) / 25600000000000000000000), D2 := ((4660575262232142941931 : Rat) / 25600000000000000000000), D3 := ((459779134732142868527 : Rat) / 5120000000000000000000), D4 := ((135468108660713955459 : Rat) / 3200000000000000000000), LB := ((4125205081412231 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70143711262232142941931 : Rat) / 25600000000000000000000), R := ((35074131765446428613879 : Rat) / 12800000000000000000000), D0 := ((35074131765446428613879 : Rat) / 12800000000000000000000), D1 := ((11810450485446428613879 : Rat) / 12800000000000000000000), D2 := ((2332563765446428613879 : Rat) / 12800000000000000000000), D3 := ((1151723971160714314231 : Rat) / 12800000000000000000000), D4 := ((215838520124999471569 : Rat) / 5120000000000000000000), LB := ((10665454656862139 : Rat) / 25000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35074131765446428613879 : Rat) / 12800000000000000000000), R := ((14030563159910714302717 : Rat) / 5120000000000000000000), D0 := ((14030563159910714302717 : Rat) / 5120000000000000000000), D1 := ((4725090647910714302717 : Rat) / 5120000000000000000000), D2 := ((933935959910714302717 : Rat) / 5120000000000000000000), D3 := ((2308000210982142914289 : Rat) / 25600000000000000000000), D4 := ((537320165982141536009 : Rat) / 12800000000000000000000), LB := ((5550623703137747 : Rat) / 12500000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((14030563159910714302717 : Rat) / 5120000000000000000000), R := ((17539342017053571449853 : Rat) / 6400000000000000000000), D0 := ((17539342017053571449853 : Rat) / 6400000000000000000000), D1 := ((5907501377053571449853 : Rat) / 6400000000000000000000), D2 := ((1168558017053571449853 : Rat) / 6400000000000000000000), D3 := ((578138119910714300029 : Rat) / 6400000000000000000000), D4 := ((1070088063303568786191 : Rat) / 25600000000000000000000), LB := ((46483492443843977 : Rat) / 100000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((17539342017053571449853 : Rat) / 6400000000000000000000), R := ((70161920336875000085239 : Rat) / 25600000000000000000000), D0 := ((70161920336875000085239 : Rat) / 25600000000000000000000), D1 := ((23634557776875000085239 : Rat) / 25600000000000000000000), D2 := ((4678784336875000085239 : Rat) / 25600000000000000000000), D3 := ((2317104748303571485943 : Rat) / 25600000000000000000000), D4 := ((266383948660713625091 : Rat) / 6400000000000000000000), LB := ((2444964272274863 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70161920336875000085239 : Rat) / 25600000000000000000000), R := ((35083236302767857185533 : Rat) / 12800000000000000000000), D0 := ((35083236302767857185533 : Rat) / 12800000000000000000000), D1 := ((11819555022767857185533 : Rat) / 12800000000000000000000), D2 := ((2341668302767857185533 : Rat) / 12800000000000000000000), D3 := ((232165701696428577177 : Rat) / 2560000000000000000000), D4 := ((1060983525982140214537 : Rat) / 25600000000000000000000), LB := ((2582717859359873 : Rat) / 5000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((35083236302767857185533 : Rat) / 12800000000000000000000), R := ((70171024874196428656893 : Rat) / 25600000000000000000000), D0 := ((70171024874196428656893 : Rat) / 25600000000000000000000), D1 := ((23643662314196428656893 : Rat) / 25600000000000000000000), D2 := ((4687888874196428656893 : Rat) / 25600000000000000000000), D3 := ((2326209285625000057597 : Rat) / 25600000000000000000000), D4 := ((105643125732142592871 : Rat) / 2560000000000000000000), LB := ((5475072690138139 : Rat) / 10000000000000000000) },
  { w1 := ((8068130959934263 : Rat) / 10000000000000000), w2 := ((10298553719643791 : Rat) / 250000000000000000), w3 := ((2139055443501027 : Rat) / 12500000000000000), w4 := ((728430234131617 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132509405446428571483 : Rat) / 50000000000000000000), s4 := ((34776808526785713037 : Rat) / 12500000000000000000), L := ((70171024874196428656893 : Rat) / 25600000000000000000000), R := ((13706167410714285731 : Rat) / 5000000000000000000), D0 := ((13706167410714285731 : Rat) / 5000000000000000000), D1 := ((4618791910714285731 : Rat) / 5000000000000000000), D2 := ((916492410714285731 : Rat) / 5000000000000000000), D3 := ((4552268660714285827 : Rat) / 50000000000000000000), D4 := ((1051878988660711642883 : Rat) / 25600000000000000000000), LB := ((5819044498718839 : Rat) / 10000000000000000000) }
]

def block390RightChunk001L : Rat := ((1614864603 : Rat) / 640000000)
def block390RightChunk001R : Rat := ((13706167410714285731 : Rat) / 5000000000000000000)

def block390RightChunk001Certificate : Bool :=
  allBoxesValid block390RightChunk001 &&
  coversFromBool block390RightChunk001 block390RightChunk001L block390RightChunk001R

theorem block390RightChunk001Certificate_eq_true :
    block390RightChunk001Certificate = true := by
  native_decide

def block390RightChainCertificate : Bool :=
  decide (
    block390RightL = ((87051899553571428739 : Rat) / 50000000000000000000) /\
    ((1614864603 : Rat) / 640000000) = ((1614864603 : Rat) / 640000000) /\
    ((13706167410714285731 : Rat) / 5000000000000000000) = block390RightR)

theorem block390RightChainCertificate_eq_true :
    block390RightChainCertificate = true := by
  native_decide

def block390LeftBoxCount : Nat := boxCount block390LeftBoxes
def block390RightBoxCount : Nat := 151

def block390_rational_certificate : Prop :=
    block390LeftCertificate = true /\
    block390RightChainCertificate = true /\
    block390RightChunk000Certificate = true /\
    block390RightChunk001Certificate = true

theorem block390_rational_certificate_proof :
    block390_rational_certificate := by
  exact ⟨block390LeftCertificate_eq_true, block390RightChainCertificate_eq_true, block390RightChunk000Certificate_eq_true, block390RightChunk001Certificate_eq_true⟩

end Block390
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block390

open Set

def block390W1 : Rat := ((8068130959934263 : Rat) / 10000000000000000)
def block390W2 : Rat := ((10298553719643791 : Rat) / 250000000000000000)
def block390W3 : Rat := ((2139055443501027 : Rat) / 12500000000000000)
def block390W4 : Rat := ((728430234131617 : Rat) / 5000000000000000)
def block390S1 : Rat := ((18174751 : Rat) / 10000000)
def block390S2 : Rat := ((511587 : Rat) / 200000)
def block390S3 : Rat := ((132509405446428571483 : Rat) / 50000000000000000000)
def block390S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block390V (y : ℝ) : ℝ :=
  ratPotential block390W1 block390W2 block390W3 block390W4 block390S1 block390S2 block390S3 block390S4 y

def block390LeftParamsCertificate : Bool :=
  allBoxesSameParams block390LeftBoxes block390W1 block390W2 block390W3 block390W4 block390S1 block390S2 block390S3 block390S4

theorem block390LeftParamsCertificate_eq_true :
    block390LeftParamsCertificate = true := by
  native_decide

theorem block390_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block390LeftL : ℝ) (block390LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block390S1 : ℝ))
    (hy2ne : y ≠ (block390S2 : ℝ))
    (hy3ne : y ≠ (block390S3 : ℝ))
    (hy4ne : y ≠ (block390S4 : ℝ)) :
    0 < block390V y := by
  have hcert := block390LeftCertificate_eq_true
  unfold block390LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block390LeftBoxes) (lo := block390LeftL) (hi := block390LeftR)
    (w1 := block390W1) (w2 := block390W2) (w3 := block390W3) (w4 := block390W4)
    (s1 := block390S1) (s2 := block390S2) (s3 := block390S3) (s4 := block390S4)
    hboxes hcover block390LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block390RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block390RightChunk000 block390W1 block390W2 block390W3 block390W4 block390S1 block390S2 block390S3 block390S4

theorem block390RightChunk000ParamsCertificate_eq_true :
    block390RightChunk000ParamsCertificate = true := by
  native_decide

theorem block390_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block390RightChunk000L : ℝ) (block390RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block390S1 : ℝ))
    (hy2ne : y ≠ (block390S2 : ℝ))
    (hy3ne : y ≠ (block390S3 : ℝ))
    (hy4ne : y ≠ (block390S4 : ℝ)) :
    0 < block390V y := by
  have hcert := block390RightChunk000Certificate_eq_true
  unfold block390RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block390RightChunk000) (lo := block390RightChunk000L) (hi := block390RightChunk000R)
    (w1 := block390W1) (w2 := block390W2) (w3 := block390W3) (w4 := block390W4)
    (s1 := block390S1) (s2 := block390S2) (s3 := block390S3) (s4 := block390S4)
    hboxes hcover block390RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block390RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block390RightChunk001 block390W1 block390W2 block390W3 block390W4 block390S1 block390S2 block390S3 block390S4

theorem block390RightChunk001ParamsCertificate_eq_true :
    block390RightChunk001ParamsCertificate = true := by
  native_decide

theorem block390_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block390RightChunk001L : ℝ) (block390RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block390S1 : ℝ))
    (hy2ne : y ≠ (block390S2 : ℝ))
    (hy3ne : y ≠ (block390S3 : ℝ))
    (hy4ne : y ≠ (block390S4 : ℝ)) :
    0 < block390V y := by
  have hcert := block390RightChunk001Certificate_eq_true
  unfold block390RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block390RightChunk001) (lo := block390RightChunk001L) (hi := block390RightChunk001R)
    (w1 := block390W1) (w2 := block390W2) (w3 := block390W3) (w4 := block390W4)
    (s1 := block390S1) (s2 := block390S2) (s3 := block390S3) (s4 := block390S4)
    hboxes hcover block390RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block390_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block390RightL : ℝ) (block390RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block390S1 : ℝ))
    (hy2ne : y ≠ (block390S2 : ℝ))
    (hy3ne : y ≠ (block390S3 : ℝ))
    (hy4ne : y ≠ (block390S4 : ℝ)) :
    0 < block390V y := by
  by_cases h0 : y ≤ (block390RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block390RightChunk000L : ℝ) (block390RightChunk000R : ℝ) := by
      have hL : (block390RightChunk000L : ℝ) = (block390RightL : ℝ) := by
        norm_num [block390RightChunk000L, block390RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block390_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block390RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block390RightChunk001L : ℝ) = (block390RightChunk000R : ℝ) := by
      norm_num [block390RightChunk001L, block390RightChunk000R]
    have hR : (block390RightChunk001R : ℝ) = (block390RightR : ℝ) := by
      norm_num [block390RightChunk001R, block390RightR]
    have hyc : y ∈ Icc (block390RightChunk001L : ℝ) (block390RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block390_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block390_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block390LeftL : ℝ) (block390LeftR : ℝ) →
    y ≠ 0 → y ≠ (block390S1 : ℝ) → y ≠ (block390S2 : ℝ) →
    y ≠ (block390S3 : ℝ) → y ≠ (block390S4 : ℝ) → 0 < block390V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block390RightL : ℝ) (block390RightR : ℝ) →
    y ≠ 0 → y ≠ (block390S1 : ℝ) → y ≠ (block390S2 : ℝ) →
    y ≠ (block390S3 : ℝ) → y ≠ (block390S4 : ℝ) → 0 < block390V y)

theorem block390_reallog_certificate_proof :
    block390_reallog_certificate := by
  exact ⟨block390_left_V_pos, block390_right_V_pos⟩

end Block390
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block390.block390V
#check Erdos1038Lean.M1817475.Block390.block390_left_V_pos
#check Erdos1038Lean.M1817475.Block390.block390_right_V_pos
#check Erdos1038Lean.M1817475.Block390.block390_reallog_certificate_proof
