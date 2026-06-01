/-
Self-contained Lean4Web paste file.
Block 6 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block006

def block006LeftL : Rat := ((40805328125000000003 : Rat) / 50000000000000000000)
def block006LeftR : Rat := ((20407551339285714287 : Rat) / 25000000000000000000)
def block006RightL : Rat := ((90805328125000000003 : Rat) / 50000000000000000000)
def block006RightR : Rat := ((70407551339285714287 : Rat) / 25000000000000000000)

def block006LeftBoxes : List RatBox := [
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((40805328125000000003 : Rat) / 50000000000000000000), R := ((20407551339285714287 : Rat) / 25000000000000000000), D0 := ((20407551339285714287 : Rat) / 25000000000000000000), D1 := ((50068426874999999997 : Rat) / 50000000000000000000), D2 := ((87091421874999999997 : Rat) / 50000000000000000000), D3 := ((92945445624999999997 : Rat) / 50000000000000000000), D4 := ((100765093482142852037 : Rat) / 50000000000000000000), LB := ((6164640544355199 : Rat) / 500000000000000000) }
]

def block006LeftCertificate : Bool :=
  allBoxesValid block006LeftBoxes &&
  coversFromBool block006LeftBoxes block006LeftL block006LeftR

theorem block006LeftCertificate_eq_true :
    block006LeftCertificate = true := by
  native_decide

def block006RightChunk000 : List RatBox := [
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((90805328125000000003 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((68426874999999997 : Rat) / 50000000000000000000), D2 := ((37091421874999999997 : Rat) / 50000000000000000000), D3 := ((42945445624999999997 : Rat) / 50000000000000000000), D4 := ((50765093482142852037 : Rat) / 50000000000000000000), LB := ((701724068572911 : Rat) / 10000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((1267416665178571301 : Rat) / 1250000000000000000), LB := ((24356262202240617 : Rat) / 10000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((511587 : Rat) / 200000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((341841790178571301 : Rat) / 1250000000000000000), LB := ((1068195164446631 : Rat) / 1000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((137282938214285714287 : Rat) / 50000000000000000000), D0 := ((137282938214285714287 : Rat) / 50000000000000000000), D1 := ((46409183214285714287 : Rat) / 50000000000000000000), D2 := ((9386188214285714287 : Rat) / 50000000000000000000), D3 := ((3532164464285714287 : Rat) / 50000000000000000000), D4 := ((195491196428571301 : Rat) / 1250000000000000000), LB := ((456091642396969 : Rat) / 1562500000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((137282938214285714287 : Rat) / 50000000000000000000), R := ((278098040892857142861 : Rat) / 100000000000000000000), D0 := ((278098040892857142861 : Rat) / 100000000000000000000), D1 := ((96350530892857142861 : Rat) / 100000000000000000000), D2 := ((22304540892857142861 : Rat) / 100000000000000000000), D3 := ((10596493392857142861 : Rat) / 100000000000000000000), D4 := ((4287483392857137753 : Rat) / 50000000000000000000), LB := ((4756449846906319 : Rat) / 500000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((278098040892857142861 : Rat) / 100000000000000000000), R := ((1115924328035714285731 : Rat) / 400000000000000000000), D0 := ((1115924328035714285731 : Rat) / 400000000000000000000), D1 := ((388934288035714285731 : Rat) / 400000000000000000000), D2 := ((92750328035714285731 : Rat) / 400000000000000000000), D3 := ((45918138035714285731 : Rat) / 400000000000000000000), D4 := ((5042802321428561219 : Rat) / 100000000000000000000), LB := ((18274913506352797 : Rat) / 500000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1115924328035714285731 : Rat) / 400000000000000000000), R := ((2235380820535714285749 : Rat) / 800000000000000000000), D0 := ((2235380820535714285749 : Rat) / 800000000000000000000), D1 := ((781400740535714285749 : Rat) / 800000000000000000000), D2 := ((189032820535714285749 : Rat) / 800000000000000000000), D3 := ((95368440535714285749 : Rat) / 800000000000000000000), D4 := ((16639044821428530589 : Rat) / 400000000000000000000), LB := ((8044650621126609 : Rat) / 250000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2235380820535714285749 : Rat) / 800000000000000000000), R := ((559728246250000000009 : Rat) / 200000000000000000000), D0 := ((559728246250000000009 : Rat) / 200000000000000000000), D1 := ((196233226250000000009 : Rat) / 200000000000000000000), D2 := ((48141246250000000009 : Rat) / 200000000000000000000), D3 := ((24725151250000000009 : Rat) / 200000000000000000000), D4 := ((29745925178571346891 : Rat) / 800000000000000000000), LB := ((3978433448396157 : Rat) / 500000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((559728246250000000009 : Rat) / 200000000000000000000), R := ((4481358134464285714359 : Rat) / 1600000000000000000000), D0 := ((4481358134464285714359 : Rat) / 1600000000000000000000), D1 := ((1573397974464285714359 : Rat) / 1600000000000000000000), D2 := ((388662134464285714359 : Rat) / 1600000000000000000000), D3 := ((201333374464285714359 : Rat) / 1600000000000000000000), D4 := ((6553440178571408151 : Rat) / 200000000000000000000), LB := ((3378962826788623 : Rat) / 250000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4481358134464285714359 : Rat) / 1600000000000000000000), R := ((2242445149464285714323 : Rat) / 800000000000000000000), D0 := ((2242445149464285714323 : Rat) / 800000000000000000000), D1 := ((788465069464285714323 : Rat) / 800000000000000000000), D2 := ((196097149464285714323 : Rat) / 800000000000000000000), D3 := ((102432769464285714323 : Rat) / 800000000000000000000), D4 := ((48895356964285550921 : Rat) / 1600000000000000000000), LB := ((15504873080497 : Rat) / 3125000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2242445149464285714323 : Rat) / 800000000000000000000), R := ((8973312762321428571579 : Rat) / 3200000000000000000000), D0 := ((8973312762321428571579 : Rat) / 3200000000000000000000), D1 := ((3157392442321428571579 : Rat) / 3200000000000000000000), D2 := ((787920762321428571579 : Rat) / 3200000000000000000000), D3 := ((413263242321428571579 : Rat) / 3200000000000000000000), D4 := ((22681596249999918317 : Rat) / 800000000000000000000), LB := ((10736723117993341 : Rat) / 1000000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8973312762321428571579 : Rat) / 3200000000000000000000), R := ((4488422463392857142933 : Rat) / 1600000000000000000000), D0 := ((4488422463392857142933 : Rat) / 1600000000000000000000), D1 := ((1580462303392857142933 : Rat) / 1600000000000000000000), D2 := ((395726463392857142933 : Rat) / 1600000000000000000000), D3 := ((208397703392857142933 : Rat) / 1600000000000000000000), D4 := ((87194220535713958981 : Rat) / 3200000000000000000000), LB := ((7704599121027389 : Rat) / 1000000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4488422463392857142933 : Rat) / 1600000000000000000000), R := ((8980377091250000000153 : Rat) / 3200000000000000000000), D0 := ((8980377091250000000153 : Rat) / 3200000000000000000000), D1 := ((3164456771250000000153 : Rat) / 3200000000000000000000), D2 := ((794985091250000000153 : Rat) / 3200000000000000000000), D3 := ((420327571250000000153 : Rat) / 3200000000000000000000), D4 := ((41831028035714122347 : Rat) / 1600000000000000000000), LB := ((5097425548605039 : Rat) / 1000000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8980377091250000000153 : Rat) / 3200000000000000000000), R := ((224597731392857142861 : Rat) / 80000000000000000000), D0 := ((224597731392857142861 : Rat) / 80000000000000000000), D1 := ((79199723392857142861 : Rat) / 80000000000000000000), D2 := ((19962931392857142861 : Rat) / 80000000000000000000), D3 := ((10596493392857142861 : Rat) / 80000000000000000000), D4 := ((80129891607142530407 : Rat) / 3200000000000000000000), LB := ((29506180193208387 : Rat) / 10000000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((224597731392857142861 : Rat) / 80000000000000000000), R := ((8987441420178571428727 : Rat) / 3200000000000000000000), D0 := ((8987441420178571428727 : Rat) / 3200000000000000000000), D1 := ((3171521100178571428727 : Rat) / 3200000000000000000000), D2 := ((802049420178571428727 : Rat) / 3200000000000000000000), D3 := ((427391900178571428727 : Rat) / 3200000000000000000000), D4 := ((1914943178571420403 : Rat) / 80000000000000000000), LB := ((1304387977267063 : Rat) / 1000000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8987441420178571428727 : Rat) / 3200000000000000000000), R := ((4495486792321428571507 : Rat) / 1600000000000000000000), D0 := ((4495486792321428571507 : Rat) / 1600000000000000000000), D1 := ((1587526632321428571507 : Rat) / 1600000000000000000000), D2 := ((402790792321428571507 : Rat) / 1600000000000000000000), D3 := ((215462032321428571507 : Rat) / 1600000000000000000000), D4 := ((73065562678571101833 : Rat) / 3200000000000000000000), LB := ((20464838891232073 : Rat) / 100000000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4495486792321428571507 : Rat) / 1600000000000000000000), R := ((3597095866750000000063 : Rat) / 1280000000000000000000), D0 := ((3597095866750000000063 : Rat) / 1280000000000000000000), D1 := ((1270727738750000000063 : Rat) / 1280000000000000000000), D2 := ((322939066750000000063 : Rat) / 1280000000000000000000), D3 := ((173076058750000000063 : Rat) / 1280000000000000000000), D4 := ((34766699107142693773 : Rat) / 1600000000000000000000), LB := ((6148977328272021 : Rat) / 1000000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3597095866750000000063 : Rat) / 1280000000000000000000), R := ((8994505749107142857301 : Rat) / 3200000000000000000000), D0 := ((8994505749107142857301 : Rat) / 3200000000000000000000), D1 := ((3178585429107142857301 : Rat) / 3200000000000000000000), D2 := ((809113749107142857301 : Rat) / 3200000000000000000000), D3 := ((434456229107142857301 : Rat) / 3200000000000000000000), D4 := ((27106926392857012161 : Rat) / 1280000000000000000000), LB := ((3069310942001857 : Rat) / 500000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8994505749107142857301 : Rat) / 3200000000000000000000), R := ((17992543662678571428889 : Rat) / 6400000000000000000000), D0 := ((17992543662678571428889 : Rat) / 6400000000000000000000), D1 := ((6360703022678571428889 : Rat) / 6400000000000000000000), D2 := ((1621759662678571428889 : Rat) / 6400000000000000000000), D3 := ((872444622678571428889 : Rat) / 6400000000000000000000), D4 := ((66001233749999673259 : Rat) / 3200000000000000000000), LB := ((6301691285599209 : Rat) / 1000000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17992543662678571428889 : Rat) / 6400000000000000000000), R := ((2249509478392857142897 : Rat) / 800000000000000000000), D0 := ((2249509478392857142897 : Rat) / 800000000000000000000), D1 := ((795529398392857142897 : Rat) / 800000000000000000000), D2 := ((203161478392857142897 : Rat) / 800000000000000000000), D3 := ((109497098392857142897 : Rat) / 800000000000000000000), D4 := ((128470303035713632231 : Rat) / 6400000000000000000000), LB := ((830924654406387 : Rat) / 125000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2249509478392857142897 : Rat) / 800000000000000000000), R := ((72012560624285714287 : Rat) / 25600000000000000000), D0 := ((72012560624285714287 : Rat) / 25600000000000000000), D1 := ((25485198064285714287 : Rat) / 25600000000000000000), D2 := ((6529424624285714287 : Rat) / 25600000000000000000), D3 := ((3532164464285714287 : Rat) / 25600000000000000000), D4 := ((15617267321428489743 : Rat) / 800000000000000000000), LB := ((7549016600438829 : Rat) / 10000000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((72012560624285714287 : Rat) / 25600000000000000000), R := ((4502551121250000000081 : Rat) / 1600000000000000000000), D0 := ((4502551121250000000081 : Rat) / 1600000000000000000000), D1 := ((1594590961250000000081 : Rat) / 1600000000000000000000), D2 := ((409855121250000000081 : Rat) / 1600000000000000000000), D3 := ((222526361250000000081 : Rat) / 1600000000000000000000), D4 := ((11787380964285648937 : Rat) / 640000000000000000000), LB := ((307587911789739 : Rat) / 125000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4502551121250000000081 : Rat) / 1600000000000000000000), R := ((9008634406964285714449 : Rat) / 3200000000000000000000), D0 := ((9008634406964285714449 : Rat) / 3200000000000000000000), D1 := ((3192714086964285714449 : Rat) / 3200000000000000000000), D2 := ((823242406964285714449 : Rat) / 3200000000000000000000), D3 := ((448584886964285714449 : Rat) / 3200000000000000000000), D4 := ((27702370178571265199 : Rat) / 1600000000000000000000), LB := ((2540102231003649 : Rat) / 500000000000000000) },
  { w1 := ((11242826608099557 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2501050100397023 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((9008634406964285714449 : Rat) / 3200000000000000000000), R := ((70407551339285714287 : Rat) / 25000000000000000000), D0 := ((70407551339285714287 : Rat) / 25000000000000000000), D1 := ((24970673839285714287 : Rat) / 25000000000000000000), D2 := ((6459176339285714287 : Rat) / 25000000000000000000), D3 := ((3532164464285714287 : Rat) / 25000000000000000000), D4 := ((51872575892856816111 : Rat) / 3200000000000000000000), LB := ((4365912909165659 : Rat) / 500000000000000000) }
]

def block006RightChunk000L : Rat := ((90805328125000000003 : Rat) / 50000000000000000000)
def block006RightChunk000R : Rat := ((70407551339285714287 : Rat) / 25000000000000000000)

def block006RightChunk000Certificate : Bool :=
  allBoxesValid block006RightChunk000 &&
  coversFromBool block006RightChunk000 block006RightChunk000L block006RightChunk000R

theorem block006RightChunk000Certificate_eq_true :
    block006RightChunk000Certificate = true := by
  native_decide

def block006RightChainCertificate : Bool :=
  decide (
    block006RightL = ((90805328125000000003 : Rat) / 50000000000000000000) /\
    ((70407551339285714287 : Rat) / 25000000000000000000) = block006RightR)

theorem block006RightChainCertificate_eq_true :
    block006RightChainCertificate = true := by
  native_decide

def block006LeftBoxCount : Nat := boxCount block006LeftBoxes
def block006RightBoxCount : Nat := 24

def block006_rational_certificate : Prop :=
    block006LeftCertificate = true /\
    block006RightChainCertificate = true /\
    block006RightChunk000Certificate = true

theorem block006_rational_certificate_proof :
    block006_rational_certificate := by
  exact ⟨block006LeftCertificate_eq_true, block006RightChainCertificate_eq_true, block006RightChunk000Certificate_eq_true⟩

end Block006
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block006

open Set

def block006W1 : Rat := ((11242826608099557 : Rat) / 1000000000000000)
def block006W2 : Rat := (0 : Rat)
def block006W3 : Rat := (0 : Rat)
def block006W4 : Rat := ((2501050100397023 : Rat) / 10000000000000000)
def block006S1 : Rat := ((18174751 : Rat) / 10000000)
def block006S2 : Rat := ((511587 : Rat) / 200000)
def block006S3 : Rat := ((107000619 : Rat) / 40000000)
def block006S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block006V (y : ℝ) : ℝ :=
  ratPotential block006W1 block006W2 block006W3 block006W4 block006S1 block006S2 block006S3 block006S4 y

def block006LeftParamsCertificate : Bool :=
  allBoxesSameParams block006LeftBoxes block006W1 block006W2 block006W3 block006W4 block006S1 block006S2 block006S3 block006S4

theorem block006LeftParamsCertificate_eq_true :
    block006LeftParamsCertificate = true := by
  native_decide

theorem block006_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block006LeftL : ℝ) (block006LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block006S1 : ℝ))
    (hy2ne : y ≠ (block006S2 : ℝ))
    (hy3ne : y ≠ (block006S3 : ℝ))
    (hy4ne : y ≠ (block006S4 : ℝ)) :
    0 < block006V y := by
  have hcert := block006LeftCertificate_eq_true
  unfold block006LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block006LeftBoxes) (lo := block006LeftL) (hi := block006LeftR)
    (w1 := block006W1) (w2 := block006W2) (w3 := block006W3) (w4 := block006W4)
    (s1 := block006S1) (s2 := block006S2) (s3 := block006S3) (s4 := block006S4)
    hboxes hcover block006LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block006RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block006RightChunk000 block006W1 block006W2 block006W3 block006W4 block006S1 block006S2 block006S3 block006S4

theorem block006RightChunk000ParamsCertificate_eq_true :
    block006RightChunk000ParamsCertificate = true := by
  native_decide

theorem block006_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block006RightChunk000L : ℝ) (block006RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block006S1 : ℝ))
    (hy2ne : y ≠ (block006S2 : ℝ))
    (hy3ne : y ≠ (block006S3 : ℝ))
    (hy4ne : y ≠ (block006S4 : ℝ)) :
    0 < block006V y := by
  have hcert := block006RightChunk000Certificate_eq_true
  unfold block006RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block006RightChunk000) (lo := block006RightChunk000L) (hi := block006RightChunk000R)
    (w1 := block006W1) (w2 := block006W2) (w3 := block006W3) (w4 := block006W4)
    (s1 := block006S1) (s2 := block006S2) (s3 := block006S3) (s4 := block006S4)
    hboxes hcover block006RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block006_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block006RightL : ℝ) (block006RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block006S1 : ℝ))
    (hy2ne : y ≠ (block006S2 : ℝ))
    (hy3ne : y ≠ (block006S3 : ℝ))
    (hy4ne : y ≠ (block006S4 : ℝ)) :
    0 < block006V y := by
  have hL : (block006RightChunk000L : ℝ) = (block006RightL : ℝ) := by
    norm_num [block006RightChunk000L, block006RightL]
  have hR : (block006RightChunk000R : ℝ) = (block006RightR : ℝ) := by
    norm_num [block006RightChunk000R, block006RightR]
  have hyc : y ∈ Icc (block006RightChunk000L : ℝ) (block006RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block006_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block006_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block006LeftL : ℝ) (block006LeftR : ℝ) →
    y ≠ 0 → y ≠ (block006S1 : ℝ) → y ≠ (block006S2 : ℝ) →
    y ≠ (block006S3 : ℝ) → y ≠ (block006S4 : ℝ) → 0 < block006V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block006RightL : ℝ) (block006RightR : ℝ) →
    y ≠ 0 → y ≠ (block006S1 : ℝ) → y ≠ (block006S2 : ℝ) →
    y ≠ (block006S3 : ℝ) → y ≠ (block006S4 : ℝ) → 0 < block006V y)

theorem block006_reallog_certificate_proof :
    block006_reallog_certificate := by
  exact ⟨block006_left_V_pos, block006_right_V_pos⟩

end Block006
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block006.block006V
#check Erdos1038Lean.M1817475.Block006.block006_left_V_pos
#check Erdos1038Lean.M1817475.Block006.block006_right_V_pos
#check Erdos1038Lean.M1817475.Block006.block006_reallog_certificate_proof
