/-
Self-contained Lean4Web paste file.
Block 347 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block347

def block347LeftL : Rat := ((9368051339285714323 : Rat) / 12500000000000000000)
def block347LeftR : Rat := ((37481979910714285863 : Rat) / 50000000000000000000)
def block347RightL : Rat := ((21868051339285714323 : Rat) / 12500000000000000000)
def block347RightR : Rat := ((137481979910714285863 : Rat) / 50000000000000000000)

def block347LeftBoxes : List RatBox := [
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((9368051339285714323 : Rat) / 12500000000000000000), R := ((37481979910714285863 : Rat) / 50000000000000000000), D0 := ((37481979910714285863 : Rat) / 50000000000000000000), D1 := ((13350387410714285677 : Rat) / 12500000000000000000), D2 := ((22606136160714285677 : Rat) / 12500000000000000000), D3 := ((95877811696428571297 : Rat) / 50000000000000000000), D4 := ((50573150535714283153 : Rat) / 25000000000000000000), LB := ((3136928968495989 : Rat) / 500000000000000000) }
]

def block347LeftCertificate : Bool :=
  allBoxesValid block347LeftBoxes &&
  coversFromBool block347LeftBoxes block347LeftL block347LeftR

theorem block347LeftCertificate_eq_true :
    block347LeftCertificate = true := by
  native_decide

def block347RightChunk000 : List RatBox := [
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21868051339285714323 : Rat) / 12500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((850387410714285677 : Rat) / 12500000000000000000), D2 := ((10106136160714285677 : Rat) / 12500000000000000000), D3 := ((45877811696428571297 : Rat) / 50000000000000000000), D4 := ((25573150535714283153 : Rat) / 25000000000000000000), LB := ((375055301693843 : Rat) / 200000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42476262053571428589 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((4219423196146927 : Rat) / 25000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23964764553571428589 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((436371585892191 : Rat) / 4000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19336890178571428589 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((7124788596111017 : Rat) / 100000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17022952991071428589 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((1663668944648207 : Rat) / 125000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14709015803571428589 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((3428594139759801 : Rat) / 250000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13552047209821428589 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((1753543108530259 : Rat) / 100000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12973562912946428589 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((9310014618441081 : Rat) / 1000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12395078616071428589 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((2160697285164631 : Rat) / 1000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11816594319196428589 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((3511269408261977 : Rat) / 500000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11527352170758928589 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((879694289016103 : Rat) / 200000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11238110022321428589 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((21003653774032127 : Rat) / 10000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10948867873883928589 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((14415229596043133 : Rat) / 100000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10659625725446428589 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((3845067744135261 : Rat) / 1000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10515004651227678589 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((633722839721701 : Rat) / 200000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10370383577008928589 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((12952420753037097 : Rat) / 5000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10225762502790178589 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((528457331924817 : Rat) / 250000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10081141428571428589 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((17420574695979907 : Rat) / 10000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9936520354352678589 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((739430830956761 : Rat) / 500000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9791899280133928589 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((20753973212587 : Rat) / 15625000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9647278205915178589 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((12946065034532273 : Rat) / 10000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9502657131696428589 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((3456736073485997 : Rat) / 2500000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9358036057477678589 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((798876708163837 : Rat) / 500000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9213414983258928589 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((19455422749269091 : Rat) / 10000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9068793909040178589 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((304052466382123 : Rat) / 125000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8924172834821428589 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((38317951073049 : Rat) / 12500000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8779551760602678589 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((3852443922175569 : Rat) / 1000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8634930686383928589 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((960446578750579 : Rat) / 200000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8490309612165178589 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((2962347634394541 : Rat) / 500000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8345688537946428589 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((1116678766655721 : Rat) / 500000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8056446389508928589 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((5485352371908697 : Rat) / 1000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7767204241071428589 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((965268942835551 : Rat) / 100000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7477962092633928589 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((2981972969085317 : Rat) / 200000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7188719944196428589 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((5916039110844429 : Rat) / 500000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6610235647321428589 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((12030889475183437 : Rat) / 1000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((517040267053571428589 : Rat) / 200000000000000000000), D0 := ((517040267053571428589 : Rat) / 200000000000000000000), D1 := ((153545247053571428589 : Rat) / 200000000000000000000), D2 := ((5453267053571428589 : Rat) / 200000000000000000000), D3 := ((5453267053571428589 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((32412331357393187 : Rat) / 10000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517040267053571428589 : Rat) / 200000000000000000000), R := ((1039533801160714285767 : Rat) / 400000000000000000000), D0 := ((1039533801160714285767 : Rat) / 400000000000000000000), D1 := ((312543761160714285767 : Rat) / 400000000000000000000), D2 := ((16359801160714285767 : Rat) / 400000000000000000000), D3 := ((16359801160714285767 : Rat) / 200000000000000000000), D4 := ((37433758660714265803 : Rat) / 200000000000000000000), LB := ((4796615628791051 : Rat) / 200000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1039533801160714285767 : Rat) / 400000000000000000000), R := ((261246767053571428589 : Rat) / 100000000000000000000), D0 := ((261246767053571428589 : Rat) / 100000000000000000000), D1 := ((79499257053571428589 : Rat) / 100000000000000000000), D2 := ((5453267053571428589 : Rat) / 100000000000000000000), D3 := ((5453267053571428589 : Rat) / 80000000000000000000), D4 := ((69414250267857103017 : Rat) / 400000000000000000000), LB := ((26704555666290763 : Rat) / 1000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261246767053571428589 : Rat) / 100000000000000000000), R := ((527946801160714285767 : Rat) / 200000000000000000000), D0 := ((527946801160714285767 : Rat) / 200000000000000000000), D1 := ((164451781160714285767 : Rat) / 200000000000000000000), D2 := ((16359801160714285767 : Rat) / 200000000000000000000), D3 := ((5453267053571428589 : Rat) / 100000000000000000000), D4 := ((15990245803571418607 : Rat) / 100000000000000000000), LB := ((10578529687090499 : Rat) / 1000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((527946801160714285767 : Rat) / 200000000000000000000), R := ((133350017053571428589 : Rat) / 50000000000000000000), D0 := ((133350017053571428589 : Rat) / 50000000000000000000), D1 := ((42476262053571428589 : Rat) / 50000000000000000000), D2 := ((5453267053571428589 : Rat) / 50000000000000000000), D3 := ((5453267053571428589 : Rat) / 200000000000000000000), D4 := ((212217796428571269 : Rat) / 1600000000000000000), LB := ((33289748256657 : Rat) / 390625000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133350017053571428589 : Rat) / 50000000000000000000), R := ((53753203107142857163 : Rat) / 20000000000000000000), D0 := ((53753203107142857163 : Rat) / 20000000000000000000), D1 := ((17403701107142857163 : Rat) / 20000000000000000000), D2 := ((2594503107142857163 : Rat) / 20000000000000000000), D3 := ((2065981428571428637 : Rat) / 100000000000000000000), D4 := ((5268489374999995009 : Rat) / 50000000000000000000), LB := ((751039139887813 : Rat) / 6250000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((53753203107142857163 : Rat) / 20000000000000000000), R := ((67707999241071428613 : Rat) / 25000000000000000000), D0 := ((67707999241071428613 : Rat) / 25000000000000000000), D1 := ((22271121741071428613 : Rat) / 25000000000000000000), D2 := ((3759624241071428613 : Rat) / 25000000000000000000), D3 := ((2065981428571428637 : Rat) / 50000000000000000000), D4 := ((8470997321428561381 : Rat) / 100000000000000000000), LB := ((2917157510997137 : Rat) / 250000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((67707999241071428613 : Rat) / 25000000000000000000), R := ((217078793857142857289 : Rat) / 80000000000000000000), D0 := ((217078793857142857289 : Rat) / 80000000000000000000), D1 := ((71680785857142857289 : Rat) / 80000000000000000000), D2 := ((12443993857142857289 : Rat) / 80000000000000000000), D3 := ((18593832857142857733 : Rat) / 400000000000000000000), D4 := ((800626986607141593 : Rat) / 12500000000000000000), LB := ((94047789784023 : Rat) / 3906250000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((217078793857142857289 : Rat) / 80000000000000000000), R := ((543729975357142857541 : Rat) / 200000000000000000000), D0 := ((543729975357142857541 : Rat) / 200000000000000000000), D1 := ((180234955357142857541 : Rat) / 200000000000000000000), D2 := ((32142975357142857541 : Rat) / 200000000000000000000), D3 := ((2065981428571428637 : Rat) / 40000000000000000000), D4 := ((23554082142857102339 : Rat) / 400000000000000000000), LB := ((11402645023650293 : Rat) / 1000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((543729975357142857541 : Rat) / 200000000000000000000), R := ((1089525932142857143719 : Rat) / 400000000000000000000), D0 := ((1089525932142857143719 : Rat) / 400000000000000000000), D1 := ((362535892142857143719 : Rat) / 400000000000000000000), D2 := ((66351932142857143719 : Rat) / 400000000000000000000), D3 := ((22725795714285715007 : Rat) / 400000000000000000000), D4 := ((10744050357142836851 : Rat) / 200000000000000000000), LB := ((13655586898761451 : Rat) / 10000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1089525932142857143719 : Rat) / 400000000000000000000), R := ((87244713828571428643 : Rat) / 32000000000000000000), D0 := ((87244713828571428643 : Rat) / 32000000000000000000), D1 := ((29085510628571428643 : Rat) / 32000000000000000000), D2 := ((5390793828571428643 : Rat) / 32000000000000000000), D3 := ((47517572857142858651 : Rat) / 800000000000000000000), D4 := ((3884423857142849013 : Rat) / 80000000000000000000), LB := ((8949019801096969 : Rat) / 2000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87244713828571428643 : Rat) / 32000000000000000000), R := ((272897978392857143089 : Rat) / 100000000000000000000), D0 := ((272897978392857143089 : Rat) / 100000000000000000000), D1 := ((91150468392857143089 : Rat) / 100000000000000000000), D2 := ((17104478392857143089 : Rat) / 100000000000000000000), D3 := ((6197944285714285911 : Rat) / 100000000000000000000), D4 := ((36778257142857061493 : Rat) / 800000000000000000000), LB := ((587347576993813 : Rat) / 400000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272897978392857143089 : Rat) / 100000000000000000000), R := ((4368433635714285718061 : Rat) / 1600000000000000000000), D0 := ((4368433635714285718061 : Rat) / 1600000000000000000000), D1 := ((1460473475714285718061 : Rat) / 1600000000000000000000), D2 := ((275737635714285718061 : Rat) / 1600000000000000000000), D3 := ((101233090000000003213 : Rat) / 1600000000000000000000), D4 := ((4339034464285704107 : Rat) / 100000000000000000000), LB := ((2140862006200367 : Rat) / 500000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4368433635714285718061 : Rat) / 1600000000000000000000), R := ((2185249808571428573349 : Rat) / 800000000000000000000), D0 := ((2185249808571428573349 : Rat) / 800000000000000000000), D1 := ((731269728571428573349 : Rat) / 800000000000000000000), D2 := ((138901808571428573349 : Rat) / 800000000000000000000), D3 := ((2065981428571428637 : Rat) / 32000000000000000000), D4 := ((2694342799999993483 : Rat) / 64000000000000000000), LB := ((2092681946273961 : Rat) / 625000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2185249808571428573349 : Rat) / 800000000000000000000), R := ((874513119714285715067 : Rat) / 320000000000000000000), D0 := ((874513119714285715067 : Rat) / 320000000000000000000), D1 := ((292921087714285715067 : Rat) / 320000000000000000000), D2 := ((55973919714285715067 : Rat) / 320000000000000000000), D3 := ((105365052857142860487 : Rat) / 1600000000000000000000), D4 := ((32646294285714204219 : Rat) / 800000000000000000000), LB := ((5217476392205711 : Rat) / 2000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((874513119714285715067 : Rat) / 320000000000000000000), R := ((1093657895000000000993 : Rat) / 400000000000000000000), D0 := ((1093657895000000000993 : Rat) / 400000000000000000000), D1 := ((366667855000000000993 : Rat) / 400000000000000000000), D2 := ((70483895000000000993 : Rat) / 400000000000000000000), D3 := ((26857758571428572281 : Rat) / 400000000000000000000), D4 := ((63226607142856979801 : Rat) / 1600000000000000000000), LB := ((20690846802720597 : Rat) / 10000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1093657895000000000993 : Rat) / 400000000000000000000), R := ((4376697561428571432609 : Rat) / 1600000000000000000000), D0 := ((4376697561428571432609 : Rat) / 1600000000000000000000), D1 := ((1468737401428571432609 : Rat) / 1600000000000000000000), D2 := ((284001561428571432609 : Rat) / 1600000000000000000000), D3 := ((109497015714285717761 : Rat) / 1600000000000000000000), D4 := ((15290156428571387791 : Rat) / 400000000000000000000), LB := ((434078969049137 : Rat) / 250000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4376697561428571432609 : Rat) / 1600000000000000000000), R := ((2189381771428571430623 : Rat) / 800000000000000000000), D0 := ((2189381771428571430623 : Rat) / 800000000000000000000), D1 := ((735401691428571430623 : Rat) / 800000000000000000000), D2 := ((143033771428571430623 : Rat) / 800000000000000000000), D3 := ((55781498571428573199 : Rat) / 800000000000000000000), D4 := ((59094644285714122527 : Rat) / 1600000000000000000000), LB := ((8092438804192803 : Rat) / 5000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2189381771428571430623 : Rat) / 800000000000000000000), R := ((4380829524285714289883 : Rat) / 1600000000000000000000), D0 := ((4380829524285714289883 : Rat) / 1600000000000000000000), D1 := ((1472869364285714289883 : Rat) / 1600000000000000000000), D2 := ((288133524285714289883 : Rat) / 1600000000000000000000), D3 := ((22725795714285715007 : Rat) / 320000000000000000000), D4 := ((5702866285714269389 : Rat) / 160000000000000000000), LB := ((17248530657580363 : Rat) / 10000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4380829524285714289883 : Rat) / 1600000000000000000000), R := ((109572387642857142963 : Rat) / 40000000000000000000), D0 := ((109572387642857142963 : Rat) / 40000000000000000000), D1 := ((36873383642857142963 : Rat) / 40000000000000000000), D2 := ((7254987642857142963 : Rat) / 40000000000000000000), D3 := ((14461870000000000459 : Rat) / 200000000000000000000), D4 := ((54962681428571265253 : Rat) / 1600000000000000000000), LB := ((258251636906813 : Rat) / 125000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((109572387642857142963 : Rat) / 40000000000000000000), R := ((4384961487142857147157 : Rat) / 1600000000000000000000), D0 := ((4384961487142857147157 : Rat) / 1600000000000000000000), D1 := ((1477001327142857147157 : Rat) / 1600000000000000000000), D2 := ((292265487142857147157 : Rat) / 1600000000000000000000), D3 := ((117760941428571432309 : Rat) / 1600000000000000000000), D4 := ((6612087499999979577 : Rat) / 200000000000000000000), LB := ((5308201846827787 : Rat) / 2000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4384961487142857147157 : Rat) / 1600000000000000000000), R := ((2193513734285714287897 : Rat) / 800000000000000000000), D0 := ((2193513734285714287897 : Rat) / 800000000000000000000), D1 := ((739533654285714287897 : Rat) / 800000000000000000000), D2 := ((147165734285714287897 : Rat) / 800000000000000000000), D3 := ((59913461428571430473 : Rat) / 800000000000000000000), D4 := ((50830718571428407979 : Rat) / 1600000000000000000000), LB := ((7006006457072167 : Rat) / 2000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2193513734285714287897 : Rat) / 800000000000000000000), R := ((1097789857857142858267 : Rat) / 400000000000000000000), D0 := ((1097789857857142858267 : Rat) / 400000000000000000000), D1 := ((370799817857142858267 : Rat) / 400000000000000000000), D2 := ((74615857857142858267 : Rat) / 400000000000000000000), D3 := ((6197944285714285911 : Rat) / 80000000000000000000), D4 := ((24382368571428489671 : Rat) / 800000000000000000000), LB := ((6908346062722837 : Rat) / 100000000000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1097789857857142858267 : Rat) / 400000000000000000000), R := ((2197645697142857145171 : Rat) / 800000000000000000000), D0 := ((2197645697142857145171 : Rat) / 800000000000000000000), D1 := ((743665617142857145171 : Rat) / 800000000000000000000), D2 := ((151297697142857145171 : Rat) / 800000000000000000000), D3 := ((64045424285714287747 : Rat) / 800000000000000000000), D4 := ((11158193571428530517 : Rat) / 400000000000000000000), LB := ((259038840038253 : Rat) / 78125000000000000) },
  { w1 := ((9126515935711021 : Rat) / 10000000000000000), w2 := ((23776835148960583 : Rat) / 500000000000000000), w3 := ((2958861279122817 : Rat) / 20000000000000000), w4 := ((3453552535021493 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133350017053571428589 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2197645697142857145171 : Rat) / 800000000000000000000), R := ((137481979910714285863 : Rat) / 50000000000000000000), D0 := ((137481979910714285863 : Rat) / 50000000000000000000), D1 := ((46608224910714285863 : Rat) / 50000000000000000000), D2 := ((9585229910714285863 : Rat) / 50000000000000000000), D3 := ((2065981428571428637 : Rat) / 25000000000000000000), D4 := ((20250405714285632397 : Rat) / 800000000000000000000), LB := ((3961089181783839 : Rat) / 500000000000000000) }
]

def block347RightChunk000L : Rat := ((21868051339285714323 : Rat) / 12500000000000000000)
def block347RightChunk000R : Rat := ((137481979910714285863 : Rat) / 50000000000000000000)

def block347RightChunk000Certificate : Bool :=
  allBoxesValid block347RightChunk000 &&
  coversFromBool block347RightChunk000 block347RightChunk000L block347RightChunk000R

theorem block347RightChunk000Certificate_eq_true :
    block347RightChunk000Certificate = true := by
  native_decide

def block347RightChainCertificate : Bool :=
  decide (
    block347RightL = ((21868051339285714323 : Rat) / 12500000000000000000) /\
    ((137481979910714285863 : Rat) / 50000000000000000000) = block347RightR)

theorem block347RightChainCertificate_eq_true :
    block347RightChainCertificate = true := by
  native_decide

def block347LeftBoxCount : Nat := boxCount block347LeftBoxes
def block347RightBoxCount : Nat := 60

def block347_rational_certificate : Prop :=
    block347LeftCertificate = true /\
    block347RightChainCertificate = true /\
    block347RightChunk000Certificate = true

theorem block347_rational_certificate_proof :
    block347_rational_certificate := by
  exact ⟨block347LeftCertificate_eq_true, block347RightChainCertificate_eq_true, block347RightChunk000Certificate_eq_true⟩

end Block347
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block347

open Set

def block347W1 : Rat := ((9126515935711021 : Rat) / 10000000000000000)
def block347W2 : Rat := ((23776835148960583 : Rat) / 500000000000000000)
def block347W3 : Rat := ((2958861279122817 : Rat) / 20000000000000000)
def block347W4 : Rat := ((3453552535021493 : Rat) / 25000000000000000)
def block347S1 : Rat := ((18174751 : Rat) / 10000000)
def block347S2 : Rat := ((511587 : Rat) / 200000)
def block347S3 : Rat := ((133350017053571428589 : Rat) / 50000000000000000000)
def block347S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block347V (y : ℝ) : ℝ :=
  ratPotential block347W1 block347W2 block347W3 block347W4 block347S1 block347S2 block347S3 block347S4 y

def block347LeftParamsCertificate : Bool :=
  allBoxesSameParams block347LeftBoxes block347W1 block347W2 block347W3 block347W4 block347S1 block347S2 block347S3 block347S4

theorem block347LeftParamsCertificate_eq_true :
    block347LeftParamsCertificate = true := by
  native_decide

theorem block347_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block347LeftL : ℝ) (block347LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block347S1 : ℝ))
    (hy2ne : y ≠ (block347S2 : ℝ))
    (hy3ne : y ≠ (block347S3 : ℝ))
    (hy4ne : y ≠ (block347S4 : ℝ)) :
    0 < block347V y := by
  have hcert := block347LeftCertificate_eq_true
  unfold block347LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block347LeftBoxes) (lo := block347LeftL) (hi := block347LeftR)
    (w1 := block347W1) (w2 := block347W2) (w3 := block347W3) (w4 := block347W4)
    (s1 := block347S1) (s2 := block347S2) (s3 := block347S3) (s4 := block347S4)
    hboxes hcover block347LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block347RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block347RightChunk000 block347W1 block347W2 block347W3 block347W4 block347S1 block347S2 block347S3 block347S4

theorem block347RightChunk000ParamsCertificate_eq_true :
    block347RightChunk000ParamsCertificate = true := by
  native_decide

theorem block347_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block347RightChunk000L : ℝ) (block347RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block347S1 : ℝ))
    (hy2ne : y ≠ (block347S2 : ℝ))
    (hy3ne : y ≠ (block347S3 : ℝ))
    (hy4ne : y ≠ (block347S4 : ℝ)) :
    0 < block347V y := by
  have hcert := block347RightChunk000Certificate_eq_true
  unfold block347RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block347RightChunk000) (lo := block347RightChunk000L) (hi := block347RightChunk000R)
    (w1 := block347W1) (w2 := block347W2) (w3 := block347W3) (w4 := block347W4)
    (s1 := block347S1) (s2 := block347S2) (s3 := block347S3) (s4 := block347S4)
    hboxes hcover block347RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block347_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block347RightL : ℝ) (block347RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block347S1 : ℝ))
    (hy2ne : y ≠ (block347S2 : ℝ))
    (hy3ne : y ≠ (block347S3 : ℝ))
    (hy4ne : y ≠ (block347S4 : ℝ)) :
    0 < block347V y := by
  have hL : (block347RightChunk000L : ℝ) = (block347RightL : ℝ) := by
    norm_num [block347RightChunk000L, block347RightL]
  have hR : (block347RightChunk000R : ℝ) = (block347RightR : ℝ) := by
    norm_num [block347RightChunk000R, block347RightR]
  have hyc : y ∈ Icc (block347RightChunk000L : ℝ) (block347RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block347_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block347_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block347LeftL : ℝ) (block347LeftR : ℝ) →
    y ≠ 0 → y ≠ (block347S1 : ℝ) → y ≠ (block347S2 : ℝ) →
    y ≠ (block347S3 : ℝ) → y ≠ (block347S4 : ℝ) → 0 < block347V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block347RightL : ℝ) (block347RightR : ℝ) →
    y ≠ 0 → y ≠ (block347S1 : ℝ) → y ≠ (block347S2 : ℝ) →
    y ≠ (block347S3 : ℝ) → y ≠ (block347S4 : ℝ) → 0 < block347V y)

theorem block347_reallog_certificate_proof :
    block347_reallog_certificate := by
  exact ⟨block347_left_V_pos, block347_right_V_pos⟩

end Block347
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block347.block347V
#check Erdos1038Lean.M1817475.Block347.block347_left_V_pos
#check Erdos1038Lean.M1817475.Block347.block347_right_V_pos
#check Erdos1038Lean.M1817475.Block347.block347_reallog_certificate_proof
