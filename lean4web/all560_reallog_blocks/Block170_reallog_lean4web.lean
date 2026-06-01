/-
Self-contained Lean4Web paste file.
Block 170 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block170

def block170LeftL : Rat := ((39202301339285714359 : Rat) / 50000000000000000000)
def block170LeftR : Rat := ((3921207589285714293 : Rat) / 5000000000000000000)
def block170RightL : Rat := ((89202301339285714359 : Rat) / 50000000000000000000)
def block170RightR : Rat := ((13921207589285714293 : Rat) / 5000000000000000000)

def block170LeftBoxes : List RatBox := [
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((39202301339285714359 : Rat) / 50000000000000000000), R := ((3921207589285714293 : Rat) / 5000000000000000000), D0 := ((3921207589285714293 : Rat) / 5000000000000000000), D1 := ((51671453660714285641 : Rat) / 50000000000000000000), D2 := ((88694448660714285641 : Rat) / 50000000000000000000), D3 := ((48422746249999999913 : Rat) / 25000000000000000000), D4 := ((100022227410714280641 : Rat) / 50000000000000000000), LB := ((20527658142587973 : Rat) / 10000000000000000000) }
]

def block170LeftCertificate : Bool :=
  allBoxesValid block170LeftBoxes &&
  coversFromBool block170LeftBoxes block170LeftL block170LeftR

theorem block170LeftCertificate_eq_true :
    block170LeftCertificate = true := by
  native_decide

def block170RightChunk000 : List RatBox := [
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((89202301339285714359 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1671453660714285641 : Rat) / 50000000000000000000), D2 := ((38694448660714285641 : Rat) / 50000000000000000000), D3 := ((23422746249999999913 : Rat) / 25000000000000000000), D4 := ((50022227410714280641 : Rat) / 50000000000000000000), LB := ((1402517420504201 : Rat) / 250000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((1049383068631219 : Rat) / 1000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((7321534920012417 : Rat) / 20000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((3895172787921987 : Rat) / 25000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((4450199198309363 : Rat) / 50000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((2417243401154817 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((227670889274193 : Rat) / 40000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((9420296072687129 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((520049531842931 : Rat) / 40000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((61086322624999968141 : Rat) / 320000000000000000000), LB := ((1043884497715749 : Rat) / 125000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((515362630336573 : Rat) / 125000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((1712835799529827 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((19274818442664987 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((23728941453212693 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((5115291608472211 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((31962137084307063 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((13190447461862431 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((105813555841891 : Rat) / 50000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((2039347601616899 : Rat) / 1250000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((11844566631853681 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((7759812529511689 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((20342788729607597 : Rat) / 50000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((779151985336457 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((7327864964021269 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((13361198423270937 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((1217272657605989 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((22182997170479 : Rat) / 20000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((10118722500651323 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((2313907716893701 : Rat) / 2500000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((850348139357221 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((7863557638300989 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((458573107976791 : Rat) / 625000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((3462827546409919 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((1326075847192687 : Rat) / 2000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((6452736522818137 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((1278830200841019 : Rat) / 2000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((3228038633612401 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((207500041174407 : Rat) / 312500000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((1389488298904229 : Rat) / 2000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((7379949419611953 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((7939110981199093 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((2156636838970133 : Rat) / 2500000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((944391606886863 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((10392912095023021 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((11475269002346467 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((12692760140127213 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((2809439974719663 : Rat) / 2000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((15540444867572223 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((17174395421303557 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((24977324857985983 : Rat) / 100000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((3254832764724297 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((5558334604925247 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((16336082539797347 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((443722387906631 : Rat) / 200000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((3393162040053571427101 : Rat) / 1280000000000000000000), D0 := ((3393162040053571427101 : Rat) / 1280000000000000000000), D1 := ((1066793912053571427101 : Rat) / 1280000000000000000000), D2 := ((119005240053571427101 : Rat) / 1280000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((143429644893453 : Rat) / 50000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3393162040053571427101 : Rat) / 1280000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 256000000000000000000), D4 := ((170985895946428444899 : Rat) / 1280000000000000000000), LB := ((35855661660533777 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((1115932607947373 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((1456705974380329 : Rat) / 500000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((5015813493975341 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((4997747573158573 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((6973260648551499 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((18892076813935843 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((430462313982142856881 : Rat) / 160000000000000000000), D0 := ((430462313982142856881 : Rat) / 160000000000000000000), D1 := ((139666297982142856881 : Rat) / 160000000000000000000), D2 := ((21192713982142856881 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((11767966042452227 : Rat) / 500000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((430462313982142856881 : Rat) / 160000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 160000000000000000000), D4 := ((15056178017857127119 : Rat) / 160000000000000000000), LB := ((11447493713621787 : Rat) / 200000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((8770665486867929 : Rat) / 100000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((109471091482142857097 : Rat) / 40000000000000000000), D0 := ((109471091482142857097 : Rat) / 40000000000000000000), D1 := ((36772087482142857097 : Rat) / 40000000000000000000), D2 := ((7153691482142857097 : Rat) / 40000000000000000000), D3 := ((632856410714285749 : Rat) / 40000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((604212864446447 : Rat) / 5000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((109471091482142857097 : Rat) / 40000000000000000000), R := ((219575039374999999943 : Rat) / 80000000000000000000), D0 := ((219575039374999999943 : Rat) / 80000000000000000000), D1 := ((74177031374999999943 : Rat) / 80000000000000000000), D2 := ((14940239374999999943 : Rat) / 80000000000000000000), D3 := ((1898569232142857247 : Rat) / 80000000000000000000), D4 := ((1908531517857138903 : Rat) / 40000000000000000000), LB := ((39583689281819 : Rat) / 625000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((219575039374999999943 : Rat) / 80000000000000000000), R := ((55051973946428571423 : Rat) / 20000000000000000000), D0 := ((55051973946428571423 : Rat) / 20000000000000000000), D1 := ((18702471946428571423 : Rat) / 20000000000000000000), D2 := ((3893273946428571423 : Rat) / 20000000000000000000), D3 := ((632856410714285749 : Rat) / 20000000000000000000), D4 := ((3184206624999992057 : Rat) / 80000000000000000000), LB := ((1507654543206649 : Rat) / 100000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((55051973946428571423 : Rat) / 20000000000000000000), R := ((441048647982142857133 : Rat) / 160000000000000000000), D0 := ((441048647982142857133 : Rat) / 160000000000000000000), D1 := ((150252631982142857133 : Rat) / 160000000000000000000), D2 := ((31779047982142857133 : Rat) / 160000000000000000000), D3 := ((5695707696428571741 : Rat) / 160000000000000000000), D4 := ((637837553571426577 : Rat) / 20000000000000000000), LB := ((862244912236143 : Rat) / 100000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((441048647982142857133 : Rat) / 160000000000000000000), R := ((176546030475000000003 : Rat) / 64000000000000000000), D0 := ((176546030475000000003 : Rat) / 64000000000000000000), D1 := ((60227624075000000003 : Rat) / 64000000000000000000), D2 := ((12838190475000000003 : Rat) / 64000000000000000000), D3 := ((12024271803571429231 : Rat) / 320000000000000000000), D4 := ((4469844017857126867 : Rat) / 160000000000000000000), LB := ((1681221920473397 : Rat) / 200000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((176546030475000000003 : Rat) / 64000000000000000000), R := ((220840752196428571441 : Rat) / 80000000000000000000), D0 := ((220840752196428571441 : Rat) / 80000000000000000000), D1 := ((75442744196428571441 : Rat) / 80000000000000000000), D2 := ((16205952196428571441 : Rat) / 80000000000000000000), D3 := ((632856410714285749 : Rat) / 16000000000000000000), D4 := ((1661366324999993597 : Rat) / 64000000000000000000), LB := ((3365482953802193 : Rat) / 1250000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((220840752196428571441 : Rat) / 80000000000000000000), R := ((1767358873982142857277 : Rat) / 640000000000000000000), D0 := ((1767358873982142857277 : Rat) / 640000000000000000000), D1 := ((604174809982142857277 : Rat) / 640000000000000000000), D2 := ((130280473982142857277 : Rat) / 640000000000000000000), D3 := ((25947112839285715709 : Rat) / 640000000000000000000), D4 := ((1918493803571420559 : Rat) / 80000000000000000000), LB := ((4303586589205821 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1767358873982142857277 : Rat) / 640000000000000000000), R := ((883995865196428571513 : Rat) / 320000000000000000000), D0 := ((883995865196428571513 : Rat) / 320000000000000000000), D1 := ((302403833196428571513 : Rat) / 320000000000000000000), D2 := ((65456665196428571513 : Rat) / 320000000000000000000), D3 := ((13289984625000000729 : Rat) / 320000000000000000000), D4 := ((14715094017857078723 : Rat) / 640000000000000000000), LB := ((141127830682021 : Rat) / 62500000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((883995865196428571513 : Rat) / 320000000000000000000), R := ((70744983472142857151 : Rat) / 25600000000000000000), D0 := ((70744983472142857151 : Rat) / 25600000000000000000), D1 := ((24217620912142857151 : Rat) / 25600000000000000000), D2 := ((5261847472142857151 : Rat) / 25600000000000000000), D3 := ((27212825660714287207 : Rat) / 640000000000000000000), D4 := ((7041118803571396487 : Rat) / 320000000000000000000), LB := ((4970880253056253 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((70744983472142857151 : Rat) / 25600000000000000000), R := ((3537882030017857143299 : Rat) / 1280000000000000000000), D0 := ((3537882030017857143299 : Rat) / 1280000000000000000000), D1 := ((1211513902017857143299 : Rat) / 1280000000000000000000), D2 := ((263725230017857143299 : Rat) / 1280000000000000000000), D3 := ((55058507732142860163 : Rat) / 1280000000000000000000), D4 := ((537975247857140289 : Rat) / 25600000000000000000), LB := ((20809703317999917 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3537882030017857143299 : Rat) / 1280000000000000000000), R := ((442314360803571428631 : Rat) / 160000000000000000000), D0 := ((442314360803571428631 : Rat) / 160000000000000000000), D1 := ((151518344803571428631 : Rat) / 160000000000000000000), D2 := ((33044760803571428631 : Rat) / 160000000000000000000), D3 := ((6961420517857143239 : Rat) / 160000000000000000000), D4 := ((26265905982142728701 : Rat) / 1280000000000000000000), LB := ((56380469415833 : Rat) / 39062500000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((442314360803571428631 : Rat) / 160000000000000000000), R := ((3539147742839285714797 : Rat) / 1280000000000000000000), D0 := ((3539147742839285714797 : Rat) / 1280000000000000000000), D1 := ((1212779614839285714797 : Rat) / 1280000000000000000000), D2 := ((264990942839285714797 : Rat) / 1280000000000000000000), D3 := ((56324220553571431661 : Rat) / 1280000000000000000000), D4 := ((3204131196428555369 : Rat) / 160000000000000000000), LB := ((692706174297 : Rat) / 781250000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3539147742839285714797 : Rat) / 1280000000000000000000), R := ((1769890299625000000273 : Rat) / 640000000000000000000), D0 := ((1769890299625000000273 : Rat) / 640000000000000000000), D1 := ((606706235625000000273 : Rat) / 640000000000000000000), D2 := ((132811899625000000273 : Rat) / 640000000000000000000), D3 := ((5695707696428571741 : Rat) / 128000000000000000000), D4 := ((25000193160714157203 : Rat) / 1280000000000000000000), LB := ((4133951652361967 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1769890299625000000273 : Rat) / 640000000000000000000), R := ((708082691132142857259 : Rat) / 256000000000000000000), D0 := ((708082691132142857259 : Rat) / 256000000000000000000), D1 := ((242809065532142857259 : Rat) / 256000000000000000000), D2 := ((53251331132142857259 : Rat) / 256000000000000000000), D3 := ((57589933375000003159 : Rat) / 1280000000000000000000), D4 := ((12183668374999935727 : Rat) / 640000000000000000000), LB := ((1311429974396039 : Rat) / 50000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((708082691132142857259 : Rat) / 256000000000000000000), R := ((7081459767732142858339 : Rat) / 2560000000000000000000), D0 := ((7081459767732142858339 : Rat) / 2560000000000000000000), D1 := ((2428723511732142858339 : Rat) / 2560000000000000000000), D2 := ((533146167732142858339 : Rat) / 2560000000000000000000), D3 := ((115812723160714292067 : Rat) / 2560000000000000000000), D4 := ((4746896067857117141 : Rat) / 256000000000000000000), LB := ((6031546838677071 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7081459767732142858339 : Rat) / 2560000000000000000000), R := ((885261578017857143011 : Rat) / 320000000000000000000), D0 := ((885261578017857143011 : Rat) / 320000000000000000000), D1 := ((303669546017857143011 : Rat) / 320000000000000000000), D2 := ((66722378017857143011 : Rat) / 320000000000000000000), D3 := ((14555697446428572227 : Rat) / 320000000000000000000), D4 := ((46836104267856885661 : Rat) / 2560000000000000000000), LB := ((1086574033547949 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((885261578017857143011 : Rat) / 320000000000000000000), R := ((7082725480553571429837 : Rat) / 2560000000000000000000), D0 := ((7082725480553571429837 : Rat) / 2560000000000000000000), D1 := ((2429989224553571429837 : Rat) / 2560000000000000000000), D2 := ((534411880553571429837 : Rat) / 2560000000000000000000), D3 := ((23415687196428572713 : Rat) / 512000000000000000000), D4 := ((5775405982142824989 : Rat) / 320000000000000000000), LB := ((99040052815913 : Rat) / 100000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7082725480553571429837 : Rat) / 2560000000000000000000), R := ((3541679168482142857793 : Rat) / 1280000000000000000000), D0 := ((3541679168482142857793 : Rat) / 1280000000000000000000), D1 := ((1215311040482142857793 : Rat) / 1280000000000000000000), D2 := ((267522368482142857793 : Rat) / 1280000000000000000000), D3 := ((58855646196428574657 : Rat) / 1280000000000000000000), D4 := ((45570391446428314163 : Rat) / 2560000000000000000000), LB := ((2295611293809119 : Rat) / 2500000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3541679168482142857793 : Rat) / 1280000000000000000000), R := ((1416798238675000000267 : Rat) / 512000000000000000000), D0 := ((1416798238675000000267 : Rat) / 512000000000000000000), D1 := ((486250987475000000267 : Rat) / 512000000000000000000), D2 := ((107135518675000000267 : Rat) / 512000000000000000000), D3 := ((118344148803571435063 : Rat) / 2560000000000000000000), D4 := ((22468767517857014207 : Rat) / 1280000000000000000000), LB := ((2176459489823951 : Rat) / 2500000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1416798238675000000267 : Rat) / 512000000000000000000), R := ((1771156012446428571771 : Rat) / 640000000000000000000), D0 := ((1771156012446428571771 : Rat) / 640000000000000000000), D1 := ((607971948446428571771 : Rat) / 640000000000000000000), D2 := ((134077612446428571771 : Rat) / 640000000000000000000), D3 := ((29744251303571430203 : Rat) / 640000000000000000000), D4 := ((8860935724999948533 : Rat) / 512000000000000000000), LB := ((529949662205903 : Rat) / 625000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1771156012446428571771 : Rat) / 640000000000000000000), R := ((7085256906196428572833 : Rat) / 2560000000000000000000), D0 := ((7085256906196428572833 : Rat) / 2560000000000000000000), D1 := ((2432520650196428572833 : Rat) / 2560000000000000000000), D2 := ((536943306196428572833 : Rat) / 2560000000000000000000), D3 := ((119609861625000006561 : Rat) / 2560000000000000000000), D4 := ((10917955553571364229 : Rat) / 640000000000000000000), LB := ((425388581830749 : Rat) / 500000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7085256906196428572833 : Rat) / 2560000000000000000000), R := ((3542944881303571429291 : Rat) / 1280000000000000000000), D0 := ((3542944881303571429291 : Rat) / 1280000000000000000000), D1 := ((1216576753303571429291 : Rat) / 1280000000000000000000), D2 := ((268788081303571429291 : Rat) / 1280000000000000000000), D3 := ((12024271803571429231 : Rat) / 256000000000000000000), D4 := ((43038965803571171167 : Rat) / 2560000000000000000000), LB := ((879708470881313 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3542944881303571429291 : Rat) / 1280000000000000000000), R := ((7086522619017857144331 : Rat) / 2560000000000000000000), D0 := ((7086522619017857144331 : Rat) / 2560000000000000000000), D1 := ((2433786363017857144331 : Rat) / 2560000000000000000000), D2 := ((538209019017857144331 : Rat) / 2560000000000000000000), D3 := ((120875574446428578059 : Rat) / 2560000000000000000000), D4 := ((21203054696428442709 : Rat) / 1280000000000000000000), LB := ((935292297255863 : Rat) / 1000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7086522619017857144331 : Rat) / 2560000000000000000000), R := ((22147360860714285719 : Rat) / 8000000000000000000), D0 := ((22147360860714285719 : Rat) / 8000000000000000000), D1 := ((7607560060714285719 : Rat) / 8000000000000000000), D2 := ((1683880860714285719 : Rat) / 8000000000000000000), D3 := ((1898569232142857247 : Rat) / 40000000000000000000), D4 := ((41773252982142599669 : Rat) / 2560000000000000000000), LB := ((2036272930295957 : Rat) / 2000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((22147360860714285719 : Rat) / 8000000000000000000), R := ((7087788331839285715829 : Rat) / 2560000000000000000000), D0 := ((7087788331839285715829 : Rat) / 2560000000000000000000), D1 := ((2435052075839285715829 : Rat) / 2560000000000000000000), D2 := ((539474731839285715829 : Rat) / 2560000000000000000000), D3 := ((122141287267857149557 : Rat) / 2560000000000000000000), D4 := ((128563739285713481 : Rat) / 8000000000000000000), LB := ((5644396857969469 : Rat) / 5000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7087788331839285715829 : Rat) / 2560000000000000000000), R := ((3544210594125000000789 : Rat) / 1280000000000000000000), D0 := ((3544210594125000000789 : Rat) / 1280000000000000000000), D1 := ((1217842466125000000789 : Rat) / 1280000000000000000000), D2 := ((270053794125000000789 : Rat) / 1280000000000000000000), D3 := ((61387071839285717653 : Rat) / 1280000000000000000000), D4 := ((40507540160714028171 : Rat) / 2560000000000000000000), LB := ((2536383564394007 : Rat) / 2000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3544210594125000000789 : Rat) / 1280000000000000000000), R := ((1772421725267857143269 : Rat) / 640000000000000000000), D0 := ((1772421725267857143269 : Rat) / 640000000000000000000), D1 := ((609237661267857143269 : Rat) / 640000000000000000000), D2 := ((135343325267857143269 : Rat) / 640000000000000000000), D3 := ((31009964125000001701 : Rat) / 640000000000000000000), D4 := ((19937341874999871211 : Rat) / 1280000000000000000000), LB := ((16256397531888567 : Rat) / 1000000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1772421725267857143269 : Rat) / 640000000000000000000), R := ((3545476306946428572287 : Rat) / 1280000000000000000000), D0 := ((3545476306946428572287 : Rat) / 1280000000000000000000), D1 := ((1219108178946428572287 : Rat) / 1280000000000000000000), D2 := ((271319506946428572287 : Rat) / 1280000000000000000000), D3 := ((62652784660714289151 : Rat) / 1280000000000000000000), D4 := ((9652242732142792731 : Rat) / 640000000000000000000), LB := ((4532054756647419 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3545476306946428572287 : Rat) / 1280000000000000000000), R := ((886527290839285714509 : Rat) / 320000000000000000000), D0 := ((886527290839285714509 : Rat) / 320000000000000000000), D1 := ((304935258839285714509 : Rat) / 320000000000000000000), D2 := ((67988090839285714509 : Rat) / 320000000000000000000), D3 := ((632856410714285749 : Rat) / 12800000000000000000), D4 := ((18671629053571299713 : Rat) / 1280000000000000000000), LB := ((10164924604365577 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((886527290839285714509 : Rat) / 320000000000000000000), R := ((709348403953571428757 : Rat) / 256000000000000000000), D0 := ((709348403953571428757 : Rat) / 256000000000000000000), D1 := ((244074778353571428757 : Rat) / 256000000000000000000), D2 := ((54517043953571428757 : Rat) / 256000000000000000000), D3 := ((63918497482142860649 : Rat) / 1280000000000000000000), D4 := ((4509693160714253491 : Rat) / 320000000000000000000), LB := ((3426464320222089 : Rat) / 2000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((709348403953571428757 : Rat) / 256000000000000000000), R := ((1773687438089285714767 : Rat) / 640000000000000000000), D0 := ((1773687438089285714767 : Rat) / 640000000000000000000), D1 := ((610503374089285714767 : Rat) / 640000000000000000000), D2 := ((136609038089285714767 : Rat) / 640000000000000000000), D3 := ((32275676946428573199 : Rat) / 640000000000000000000), D4 := ((3481183246428545643 : Rat) / 256000000000000000000), LB := ((25513333458618837 : Rat) / 10000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1773687438089285714767 : Rat) / 640000000000000000000), R := ((443580073625000000129 : Rat) / 160000000000000000000), D0 := ((443580073625000000129 : Rat) / 160000000000000000000), D1 := ((152784057625000000129 : Rat) / 160000000000000000000), D2 := ((34310473625000000129 : Rat) / 160000000000000000000), D3 := ((8227133339285714737 : Rat) / 160000000000000000000), D4 := ((8386529910714221233 : Rat) / 640000000000000000000), LB := ((1593709439959179 : Rat) / 2000000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((443580073625000000129 : Rat) / 160000000000000000000), R := ((354990630182142857253 : Rat) / 128000000000000000000), D0 := ((354990630182142857253 : Rat) / 128000000000000000000), D1 := ((122353817382142857253 : Rat) / 128000000000000000000), D2 := ((27574950182142857253 : Rat) / 128000000000000000000), D3 := ((33541389767857144697 : Rat) / 640000000000000000000), D4 := ((1938418374999983871 : Rat) / 160000000000000000000), LB := ((659251703086039 : Rat) / 200000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((354990630182142857253 : Rat) / 128000000000000000000), R := ((887793003660714286007 : Rat) / 320000000000000000000), D0 := ((887793003660714286007 : Rat) / 320000000000000000000), D1 := ((306200971660714286007 : Rat) / 320000000000000000000), D2 := ((69253803660714286007 : Rat) / 320000000000000000000), D3 := ((17087123089285715223 : Rat) / 320000000000000000000), D4 := ((1424163417857129947 : Rat) / 128000000000000000000), LB := ((3264967962465587 : Rat) / 500000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((887793003660714286007 : Rat) / 320000000000000000000), R := ((222106465017857142939 : Rat) / 80000000000000000000), D0 := ((222106465017857142939 : Rat) / 80000000000000000000), D1 := ((76708457017857142939 : Rat) / 80000000000000000000), D2 := ((17471665017857142939 : Rat) / 80000000000000000000), D3 := ((4429994875000000243 : Rat) / 80000000000000000000), D4 := ((3243980339285681993 : Rat) / 320000000000000000000), LB := ((1339727446581257 : Rat) / 250000000000000000) }
]

def block170RightChunk000L : Rat := ((89202301339285714359 : Rat) / 50000000000000000000)
def block170RightChunk000R : Rat := ((222106465017857142939 : Rat) / 80000000000000000000)

def block170RightChunk000Certificate : Bool :=
  allBoxesValid block170RightChunk000 &&
  coversFromBool block170RightChunk000 block170RightChunk000L block170RightChunk000R

theorem block170RightChunk000Certificate_eq_true :
    block170RightChunk000Certificate = true := by
  native_decide

def block170RightChunk001 : List RatBox := [
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((222106465017857142939 : Rat) / 80000000000000000000), R := ((444845786446428571627 : Rat) / 160000000000000000000), D0 := ((444845786446428571627 : Rat) / 160000000000000000000), D1 := ((154049770446428571627 : Rat) / 160000000000000000000), D2 := ((35576186446428571627 : Rat) / 160000000000000000000), D3 := ((1898569232142857247 : Rat) / 32000000000000000000), D4 := ((652780982142849061 : Rat) / 80000000000000000000), LB := ((16820507882230329 : Rat) / 2500000000000000000) },
  { w1 := ((9117180001621217 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((52397606746053 : Rat) / 312500000000000), w4 := ((10121480203185391 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((444845786446428571627 : Rat) / 160000000000000000000), R := ((13921207589285714293 : Rat) / 5000000000000000000), D0 := ((13921207589285714293 : Rat) / 5000000000000000000), D1 := ((4833832089285714293 : Rat) / 5000000000000000000), D2 := ((1131532589285714293 : Rat) / 5000000000000000000), D3 := ((632856410714285749 : Rat) / 10000000000000000000), D4 := ((672705553571412373 : Rat) / 160000000000000000000), LB := ((5180705822606163 : Rat) / 100000000000000000) }
]

def block170RightChunk001L : Rat := ((222106465017857142939 : Rat) / 80000000000000000000)
def block170RightChunk001R : Rat := ((13921207589285714293 : Rat) / 5000000000000000000)

def block170RightChunk001Certificate : Bool :=
  allBoxesValid block170RightChunk001 &&
  coversFromBool block170RightChunk001 block170RightChunk001L block170RightChunk001R

theorem block170RightChunk001Certificate_eq_true :
    block170RightChunk001Certificate = true := by
  native_decide

def block170RightChainCertificate : Bool :=
  decide (
    block170RightL = ((89202301339285714359 : Rat) / 50000000000000000000) /\
    ((222106465017857142939 : Rat) / 80000000000000000000) = ((222106465017857142939 : Rat) / 80000000000000000000) /\
    ((13921207589285714293 : Rat) / 5000000000000000000) = block170RightR)

theorem block170RightChainCertificate_eq_true :
    block170RightChainCertificate = true := by
  native_decide

def block170LeftBoxCount : Nat := boxCount block170LeftBoxes
def block170RightBoxCount : Nat := 102

def block170_rational_certificate : Prop :=
    block170LeftCertificate = true /\
    block170RightChainCertificate = true /\
    block170RightChunk000Certificate = true /\
    block170RightChunk001Certificate = true

theorem block170_rational_certificate_proof :
    block170_rational_certificate := by
  exact ⟨block170LeftCertificate_eq_true, block170RightChainCertificate_eq_true, block170RightChunk000Certificate_eq_true, block170RightChunk001Certificate_eq_true⟩

end Block170
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block170

open Set

def block170W1 : Rat := ((9117180001621217 : Rat) / 5000000000000000)
def block170W2 : Rat := (0 : Rat)
def block170W3 : Rat := ((52397606746053 : Rat) / 312500000000000)
def block170W4 : Rat := ((10121480203185391 : Rat) / 100000000000000000)
def block170S1 : Rat := ((18174751 : Rat) / 10000000)
def block170S2 : Rat := ((511587 : Rat) / 200000)
def block170S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block170S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block170V (y : ℝ) : ℝ :=
  ratPotential block170W1 block170W2 block170W3 block170W4 block170S1 block170S2 block170S3 block170S4 y

def block170LeftParamsCertificate : Bool :=
  allBoxesSameParams block170LeftBoxes block170W1 block170W2 block170W3 block170W4 block170S1 block170S2 block170S3 block170S4

theorem block170LeftParamsCertificate_eq_true :
    block170LeftParamsCertificate = true := by
  native_decide

theorem block170_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block170LeftL : ℝ) (block170LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block170S1 : ℝ))
    (hy2ne : y ≠ (block170S2 : ℝ))
    (hy3ne : y ≠ (block170S3 : ℝ))
    (hy4ne : y ≠ (block170S4 : ℝ)) :
    0 < block170V y := by
  have hcert := block170LeftCertificate_eq_true
  unfold block170LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block170LeftBoxes) (lo := block170LeftL) (hi := block170LeftR)
    (w1 := block170W1) (w2 := block170W2) (w3 := block170W3) (w4 := block170W4)
    (s1 := block170S1) (s2 := block170S2) (s3 := block170S3) (s4 := block170S4)
    hboxes hcover block170LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block170RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block170RightChunk000 block170W1 block170W2 block170W3 block170W4 block170S1 block170S2 block170S3 block170S4

theorem block170RightChunk000ParamsCertificate_eq_true :
    block170RightChunk000ParamsCertificate = true := by
  native_decide

theorem block170_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block170RightChunk000L : ℝ) (block170RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block170S1 : ℝ))
    (hy2ne : y ≠ (block170S2 : ℝ))
    (hy3ne : y ≠ (block170S3 : ℝ))
    (hy4ne : y ≠ (block170S4 : ℝ)) :
    0 < block170V y := by
  have hcert := block170RightChunk000Certificate_eq_true
  unfold block170RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block170RightChunk000) (lo := block170RightChunk000L) (hi := block170RightChunk000R)
    (w1 := block170W1) (w2 := block170W2) (w3 := block170W3) (w4 := block170W4)
    (s1 := block170S1) (s2 := block170S2) (s3 := block170S3) (s4 := block170S4)
    hboxes hcover block170RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block170RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block170RightChunk001 block170W1 block170W2 block170W3 block170W4 block170S1 block170S2 block170S3 block170S4

theorem block170RightChunk001ParamsCertificate_eq_true :
    block170RightChunk001ParamsCertificate = true := by
  native_decide

theorem block170_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block170RightChunk001L : ℝ) (block170RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block170S1 : ℝ))
    (hy2ne : y ≠ (block170S2 : ℝ))
    (hy3ne : y ≠ (block170S3 : ℝ))
    (hy4ne : y ≠ (block170S4 : ℝ)) :
    0 < block170V y := by
  have hcert := block170RightChunk001Certificate_eq_true
  unfold block170RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block170RightChunk001) (lo := block170RightChunk001L) (hi := block170RightChunk001R)
    (w1 := block170W1) (w2 := block170W2) (w3 := block170W3) (w4 := block170W4)
    (s1 := block170S1) (s2 := block170S2) (s3 := block170S3) (s4 := block170S4)
    hboxes hcover block170RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block170_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block170RightL : ℝ) (block170RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block170S1 : ℝ))
    (hy2ne : y ≠ (block170S2 : ℝ))
    (hy3ne : y ≠ (block170S3 : ℝ))
    (hy4ne : y ≠ (block170S4 : ℝ)) :
    0 < block170V y := by
  by_cases h0 : y ≤ (block170RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block170RightChunk000L : ℝ) (block170RightChunk000R : ℝ) := by
      have hL : (block170RightChunk000L : ℝ) = (block170RightL : ℝ) := by
        norm_num [block170RightChunk000L, block170RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block170_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block170RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block170RightChunk001L : ℝ) = (block170RightChunk000R : ℝ) := by
      norm_num [block170RightChunk001L, block170RightChunk000R]
    have hR : (block170RightChunk001R : ℝ) = (block170RightR : ℝ) := by
      norm_num [block170RightChunk001R, block170RightR]
    have hyc : y ∈ Icc (block170RightChunk001L : ℝ) (block170RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block170_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block170_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block170LeftL : ℝ) (block170LeftR : ℝ) →
    y ≠ 0 → y ≠ (block170S1 : ℝ) → y ≠ (block170S2 : ℝ) →
    y ≠ (block170S3 : ℝ) → y ≠ (block170S4 : ℝ) → 0 < block170V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block170RightL : ℝ) (block170RightR : ℝ) →
    y ≠ 0 → y ≠ (block170S1 : ℝ) → y ≠ (block170S2 : ℝ) →
    y ≠ (block170S3 : ℝ) → y ≠ (block170S4 : ℝ) → 0 < block170V y)

theorem block170_reallog_certificate_proof :
    block170_reallog_certificate := by
  exact ⟨block170_left_V_pos, block170_right_V_pos⟩

end Block170
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block170.block170V
#check Erdos1038Lean.M1817475.Block170.block170_left_V_pos
#check Erdos1038Lean.M1817475.Block170.block170_right_V_pos
#check Erdos1038Lean.M1817475.Block170.block170_reallog_certificate_proof
