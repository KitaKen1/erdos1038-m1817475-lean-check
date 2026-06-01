/-
Self-contained Lean4Web paste file.
Block 412 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block412

def block412LeftL : Rat := ((36836859375000000177 : Rat) / 50000000000000000000)
def block412LeftR : Rat := ((9211658482142857187 : Rat) / 12500000000000000000)
def block412RightL : Rat := ((86836859375000000177 : Rat) / 50000000000000000000)
def block412RightR : Rat := ((34211658482142857187 : Rat) / 12500000000000000000)

def block412LeftBoxes : List RatBox := [
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((36836859375000000177 : Rat) / 50000000000000000000), R := ((9211658482142857187 : Rat) / 12500000000000000000), D0 := ((9211658482142857187 : Rat) / 12500000000000000000), D1 := ((54036895624999999823 : Rat) / 50000000000000000000), D2 := ((91059890624999999823 : Rat) / 50000000000000000000), D3 := ((47621232857142857091 : Rat) / 25000000000000000000), D4 := ((102387669374999994823 : Rat) / 50000000000000000000), LB := ((6042465688365917 : Rat) / 10000000000000000000) }
]

def block412LeftCertificate : Bool :=
  allBoxesValid block412LeftBoxes &&
  coversFromBool block412LeftBoxes block412LeftL block412LeftR

theorem block412LeftCertificate_eq_true :
    block412LeftCertificate = true := by
  native_decide

def block412RightChunk000 : List RatBox := [
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((86836859375000000177 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((4036895624999999823 : Rat) / 50000000000000000000), D2 := ((41059890624999999823 : Rat) / 50000000000000000000), D3 := ((22621232857142857091 : Rat) / 25000000000000000000), D4 := ((52387669374999994823 : Rat) / 50000000000000000000), LB := ((2437414196144263 : Rat) / 2000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41205570089285714359 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((5650848925630623 : Rat) / 10000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((31949821339285714359 : Rat) / 50000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((7544261604153711 : Rat) / 100000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((22694072589285714359 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((1165702178551029 : Rat) / 12500000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((20380135401785714359 : Rat) / 50000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((1436682752529099 : Rat) / 40000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18066198214285714359 : Rat) / 50000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((1681335626472863 : Rat) / 50000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((16909229620535714359 : Rat) / 50000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((688230970677519 : Rat) / 50000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((15752261026785714359 : Rat) / 50000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((4403644639760427 : Rat) / 250000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((15173776729910714359 : Rat) / 50000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((10090171415918073 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((14595292433035714359 : Rat) / 50000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((8513759349273349 : Rat) / 2500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((14016808136160714359 : Rat) / 50000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((3739247398336837 : Rat) / 500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((13727565987723214359 : Rat) / 50000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((602026540984053 : Rat) / 125000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13438323839285714359 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((23821910350867587 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((13149081690848214359 : Rat) / 50000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((18087177471616533 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((6111442259 : Rat) / 2560000000), D0 := ((6111442259 : Rat) / 2560000000), D1 := ((1458706003 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((12859839542410714359 : Rat) / 50000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((3790538493827697 : Rat) / 1250000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6111442259 : Rat) / 2560000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((436871341 : Rat) / 2560000000), D3 := ((12715218468191964359 : Rat) / 50000000000000000000), D4 := ((3972084425781249 : Rat) / 10000000000000000), LB := ((2121688611753103 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((12570597393973214359 : Rat) / 50000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((3181438981521463 : Rat) / 2500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((12425976319754464359 : Rat) / 50000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((485838725794871 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((12274716711 : Rat) / 5120000000), D0 := ((12274716711 : Rat) / 5120000000), D1 := ((2969244199 : Rat) / 5120000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12281355245535714359 : Rat) / 50000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((267294250540253 : Rat) / 125000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12274716711 : Rat) / 5120000000), R := ((1228212131 : Rat) / 512000000), D0 := ((1228212131 : Rat) / 512000000), D1 := ((1488324399 : Rat) / 2560000000), D2 := ((821910489 : Rat) / 5120000000), D3 := ((12209044708426339359 : Rat) / 50000000000000000000), D4 := ((967712418457031 : Rat) / 2500000000000000), LB := ((2244667656393657 : Rat) / 1250000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1228212131 : Rat) / 512000000), R := ((12289525909 : Rat) / 5120000000), D0 := ((12289525909 : Rat) / 5120000000), D1 := ((2984053397 : Rat) / 5120000000), D2 := ((81450589 : Rat) / 512000000), D3 := ((12136734171316964359 : Rat) / 50000000000000000000), D4 := ((3856387566406249 : Rat) / 10000000000000000), LB := ((7346177272109511 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12289525909 : Rat) / 5120000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((807101291 : Rat) / 5120000000), D3 := ((12064423634207589359 : Rat) / 50000000000000000000), D4 := ((1920962729492187 : Rat) / 5000000000000000), LB := ((1158965909518389 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((12304335107 : Rat) / 5120000000), D0 := ((12304335107 : Rat) / 5120000000), D1 := ((599772519 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((11992113097098214359 : Rat) / 50000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((8650358558834753 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12304335107 : Rat) / 5120000000), R := ((6155869853 : Rat) / 2560000000), D0 := ((6155869853 : Rat) / 2560000000), D1 := ((1503133597 : Rat) / 2560000000), D2 := ((792292093 : Rat) / 5120000000), D3 := ((11919802559988839359 : Rat) / 50000000000000000000), D4 := ((238312577758789 : Rat) / 625000000000000), LB := ((734447699923483 : Rat) / 1250000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6155869853 : Rat) / 2560000000), R := ((2463828861 : Rat) / 1024000000), D0 := ((2463828861 : Rat) / 1024000000), D1 := ((3013671793 : Rat) / 5120000000), D2 := ((392443747 : Rat) / 2560000000), D3 := ((11847492022879464359 : Rat) / 50000000000000000000), D4 := ((3798539136718749 : Rat) / 10000000000000000), LB := ((3266482434419321 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2463828861 : Rat) / 1024000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((155496579 : Rat) / 1024000000), D3 := ((11775181485770089359 : Rat) / 50000000000000000000), D4 := ((1892038514648437 : Rat) / 5000000000000000), LB := ((4121206979690317 : Rat) / 50000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((24660502407 : Rat) / 10240000000), D0 := ((24660502407 : Rat) / 10240000000), D1 := ((6049557383 : Rat) / 10240000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((11702870948660714359 : Rat) / 50000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((1026016632459159 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24660502407 : Rat) / 10240000000), R := ((12333953503 : Rat) / 5120000000), D0 := ((12333953503 : Rat) / 5120000000), D1 := ((3028480991 : Rat) / 5120000000), D2 := ((1532751993 : Rat) / 10240000000), D3 := ((11666715680106026859 : Rat) / 50000000000000000000), D4 := ((7524767736328123 : Rat) / 20000000000000000), LB := ((458747376332759 : Rat) / 500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12333953503 : Rat) / 5120000000), R := ((4935062321 : Rat) / 2048000000), D0 := ((4935062321 : Rat) / 2048000000), D1 := ((6064366581 : Rat) / 10240000000), D2 := ((762673697 : Rat) / 5120000000), D3 := ((11630560411551339359 : Rat) / 50000000000000000000), D4 := ((938788203613281 : Rat) / 2500000000000000), LB := ((8132236555680877 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4935062321 : Rat) / 2048000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((303588559 : Rat) / 2048000000), D3 := ((11594405142996651859 : Rat) / 50000000000000000000), D4 := ((7495843521484373 : Rat) / 20000000000000000), LB := ((3566095985501963 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((24690120803 : Rat) / 10240000000), D0 := ((24690120803 : Rat) / 10240000000), D1 := ((6079175779 : Rat) / 10240000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((11558249874441964359 : Rat) / 50000000000000000000), D4 := ((3740690707031249 : Rat) / 10000000000000000), LB := ((61749741161847 : Rat) / 100000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24690120803 : Rat) / 10240000000), R := ((12348762701 : Rat) / 5120000000), D0 := ((12348762701 : Rat) / 5120000000), D1 := ((3043290189 : Rat) / 5120000000), D2 := ((1503133597 : Rat) / 10240000000), D3 := ((11522094605887276859 : Rat) / 50000000000000000000), D4 := ((7466919306640623 : Rat) / 20000000000000000), LB := ((1315186284842583 : Rat) / 2500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12348762701 : Rat) / 5120000000), R := ((24704930001 : Rat) / 10240000000), D0 := ((24704930001 : Rat) / 10240000000), D1 := ((6093984977 : Rat) / 10240000000), D2 := ((747864499 : Rat) / 5120000000), D3 := ((11485939337332589359 : Rat) / 50000000000000000000), D4 := ((1863114299804687 : Rat) / 5000000000000000), LB := ((2194834506996507 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24704930001 : Rat) / 10240000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((1488324399 : Rat) / 10240000000), D3 := ((11449784068777901859 : Rat) / 50000000000000000000), D4 := ((7437995091796873 : Rat) / 20000000000000000), LB := ((35619115597371187 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((24719739199 : Rat) / 10240000000), D0 := ((24719739199 : Rat) / 10240000000), D1 := ((244351767 : Rat) / 409600000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11413628800223214359 : Rat) / 50000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((5555280927878603 : Rat) / 20000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24719739199 : Rat) / 10240000000), R := ((12363571899 : Rat) / 5120000000), D0 := ((12363571899 : Rat) / 5120000000), D1 := ((3058099387 : Rat) / 5120000000), D2 := ((1473515201 : Rat) / 10240000000), D3 := ((11377473531668526859 : Rat) / 50000000000000000000), D4 := ((7409070876953123 : Rat) / 20000000000000000), LB := ((4074050606459323 : Rat) / 20000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12363571899 : Rat) / 5120000000), R := ((24734548397 : Rat) / 10240000000), D0 := ((24734548397 : Rat) / 10240000000), D1 := ((6123603373 : Rat) / 10240000000), D2 := ((733055301 : Rat) / 5120000000), D3 := ((11341318263113839359 : Rat) / 50000000000000000000), D4 := ((462163048095703 : Rat) / 1250000000000000), LB := ((13402375656204613 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24734548397 : Rat) / 10240000000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((1458706003 : Rat) / 10240000000), D3 := ((11305162994559151859 : Rat) / 50000000000000000000), D4 := ((7380146662109373 : Rat) / 20000000000000000), LB := ((2749802691559 : Rat) / 40000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((4949871519 : Rat) / 2048000000), D0 := ((4949871519 : Rat) / 2048000000), D1 := ((6138412571 : Rat) / 10240000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((11269007726004464359 : Rat) / 50000000000000000000), D4 := ((3682842277343749 : Rat) / 10000000000000000), LB := ((7884000334718033 : Rat) / 1000000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4949871519 : Rat) / 2048000000), R := ((49506119789 : Rat) / 20480000000), D0 := ((49506119789 : Rat) / 20480000000), D1 := ((12284229741 : Rat) / 20480000000), D2 := ((288779361 : Rat) / 2048000000), D3 := ((11232852457449776859 : Rat) / 50000000000000000000), D4 := ((7351222447265623 : Rat) / 20000000000000000), LB := ((211994117739861 : Rat) / 400000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49506119789 : Rat) / 20480000000), R := ((12378381097 : Rat) / 5120000000), D0 := ((12378381097 : Rat) / 5120000000), D1 := ((614581717 : Rat) / 1024000000), D2 := ((2880389011 : Rat) / 20480000000), D3 := ((11214774823172433109 : Rat) / 50000000000000000000), D4 := ((14687982787109371 : Rat) / 40000000000000000), LB := ((157237685909843 : Rat) / 312500000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12378381097 : Rat) / 5120000000), R := ((49520928987 : Rat) / 20480000000), D0 := ((49520928987 : Rat) / 20480000000), D1 := ((12299038939 : Rat) / 20480000000), D2 := ((718246103 : Rat) / 5120000000), D3 := ((11196697188895089359 : Rat) / 50000000000000000000), D4 := ((1834190084960937 : Rat) / 5000000000000000), LB := ((2387258972418177 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49520928987 : Rat) / 20480000000), R := ((24764166793 : Rat) / 10240000000), D0 := ((24764166793 : Rat) / 10240000000), D1 := ((6153221769 : Rat) / 10240000000), D2 := ((2865579813 : Rat) / 20480000000), D3 := ((11178619554617745609 : Rat) / 50000000000000000000), D4 := ((14659058572265621 : Rat) / 40000000000000000), LB := ((283038228880211 : Rat) / 625000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24764166793 : Rat) / 10240000000), R := ((9907147637 : Rat) / 4096000000), D0 := ((9907147637 : Rat) / 4096000000), D1 := ((12313848137 : Rat) / 20480000000), D2 := ((1429087607 : Rat) / 10240000000), D3 := ((11160541920340401859 : Rat) / 50000000000000000000), D4 := ((7322298232421873 : Rat) / 20000000000000000), LB := ((2146954980254967 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9907147637 : Rat) / 4096000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((570154123 : Rat) / 4096000000), D3 := ((11142464286063058109 : Rat) / 50000000000000000000), D4 := ((14630134357421871 : Rat) / 40000000000000000), LB := ((4070435828749941 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((49550547383 : Rat) / 20480000000), D0 := ((49550547383 : Rat) / 20480000000), D1 := ((2465731467 : Rat) / 4096000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11124386651785714359 : Rat) / 50000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((19291061926115377 : Rat) / 50000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49550547383 : Rat) / 20480000000), R := ((24778975991 : Rat) / 10240000000), D0 := ((24778975991 : Rat) / 10240000000), D1 := ((6168030967 : Rat) / 10240000000), D2 := ((2835961417 : Rat) / 20480000000), D3 := ((11106309017508370609 : Rat) / 50000000000000000000), D4 := ((14601210142578121 : Rat) / 40000000000000000), LB := ((91431571971827 : Rat) / 250000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24778975991 : Rat) / 10240000000), R := ((49565356581 : Rat) / 20480000000), D0 := ((49565356581 : Rat) / 20480000000), D1 := ((12343466533 : Rat) / 20480000000), D2 := ((1414278409 : Rat) / 10240000000), D3 := ((11088231383231026859 : Rat) / 50000000000000000000), D4 := ((7293374017578123 : Rat) / 20000000000000000), LB := ((3467610690002787 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49565356581 : Rat) / 20480000000), R := ((2478638059 : Rat) / 1024000000), D0 := ((2478638059 : Rat) / 1024000000), D1 := ((3087717783 : Rat) / 5120000000), D2 := ((2821152219 : Rat) / 20480000000), D3 := ((11070153748953683109 : Rat) / 50000000000000000000), D4 := ((14572285927734371 : Rat) / 40000000000000000), LB := ((32892793310178303 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2478638059 : Rat) / 1024000000), R := ((49580165779 : Rat) / 20480000000), D0 := ((49580165779 : Rat) / 20480000000), D1 := ((12358275731 : Rat) / 20480000000), D2 := ((140687381 : Rat) / 1024000000), D3 := ((11052076114676339359 : Rat) / 50000000000000000000), D4 := ((909863988769531 : Rat) / 2500000000000000), LB := ((1248916978915271 : Rat) / 4000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49580165779 : Rat) / 20480000000), R := ((24793785189 : Rat) / 10240000000), D0 := ((24793785189 : Rat) / 10240000000), D1 := ((1236568033 : Rat) / 2048000000), D2 := ((2806343021 : Rat) / 20480000000), D3 := ((11033998480398995609 : Rat) / 50000000000000000000), D4 := ((14543361712890621 : Rat) / 40000000000000000), LB := ((29666738178936447 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24793785189 : Rat) / 10240000000), R := ((49594974977 : Rat) / 20480000000), D0 := ((49594974977 : Rat) / 20480000000), D1 := ((12373084929 : Rat) / 20480000000), D2 := ((1399469211 : Rat) / 10240000000), D3 := ((11015920846121651859 : Rat) / 50000000000000000000), D4 := ((7264449802734373 : Rat) / 20000000000000000), LB := ((2822447356480573 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49594974977 : Rat) / 20480000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((2791533823 : Rat) / 20480000000), D3 := ((10997843211844308109 : Rat) / 50000000000000000000), D4 := ((14514437498046871 : Rat) / 40000000000000000), LB := ((13448185560299697 : Rat) / 50000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((1984391367 : Rat) / 819200000), D0 := ((1984391367 : Rat) / 819200000), D1 := ((12387894127 : Rat) / 20480000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((10979765577566964359 : Rat) / 50000000000000000000), D4 := ((3624993847656249 : Rat) / 10000000000000000), LB := ((2568267269857927 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1984391367 : Rat) / 819200000), R := ((24808594387 : Rat) / 10240000000), D0 := ((24808594387 : Rat) / 10240000000), D1 := ((6197649363 : Rat) / 10240000000), D2 := ((22213797 : Rat) / 163840000), D3 := ((10961687943289620609 : Rat) / 50000000000000000000), D4 := ((14485513283203121 : Rat) / 40000000000000000), LB := ((614590538030313 : Rat) / 2500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24808594387 : Rat) / 10240000000), R := ((49624593373 : Rat) / 20480000000), D0 := ((49624593373 : Rat) / 20480000000), D1 := ((496108133 : Rat) / 819200000), D2 := ((1384660013 : Rat) / 10240000000), D3 := ((10943610309012276859 : Rat) / 50000000000000000000), D4 := ((7235525587890623 : Rat) / 20000000000000000), LB := ((5899865547451949 : Rat) / 25000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49624593373 : Rat) / 20480000000), R := ((12407999493 : Rat) / 5120000000), D0 := ((12407999493 : Rat) / 5120000000), D1 := ((3102526981 : Rat) / 5120000000), D2 := ((2761915427 : Rat) / 20480000000), D3 := ((10925532674734933109 : Rat) / 50000000000000000000), D4 := ((14456589068359371 : Rat) / 40000000000000000), LB := ((11365220346494509 : Rat) / 50000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12407999493 : Rat) / 5120000000), R := ((49639402571 : Rat) / 20480000000), D0 := ((49639402571 : Rat) / 20480000000), D1 := ((12417512523 : Rat) / 20480000000), D2 := ((688627707 : Rat) / 5120000000), D3 := ((10907455040457589359 : Rat) / 50000000000000000000), D4 := ((1805265870117187 : Rat) / 5000000000000000), LB := ((1373550275947117 : Rat) / 6250000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49639402571 : Rat) / 20480000000), R := ((4964680717 : Rat) / 2048000000), D0 := ((4964680717 : Rat) / 2048000000), D1 := ((6212458561 : Rat) / 10240000000), D2 := ((2747106229 : Rat) / 20480000000), D3 := ((10889377406180245609 : Rat) / 50000000000000000000), D4 := ((14427664853515621 : Rat) / 40000000000000000), LB := ((21338802145226543 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4964680717 : Rat) / 2048000000), R := ((49654211769 : Rat) / 20480000000), D0 := ((49654211769 : Rat) / 20480000000), D1 := ((12432321721 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 2048000000), D3 := ((10871299771902901859 : Rat) / 50000000000000000000), D4 := ((7206601373046873 : Rat) / 20000000000000000), LB := ((10408342042495661 : Rat) / 50000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49654211769 : Rat) / 20480000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((2732297031 : Rat) / 20480000000), D3 := ((10853222137625558109 : Rat) / 50000000000000000000), D4 := ((14398740638671871 : Rat) / 40000000000000000), LB := ((2041070185868077 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((49669020967 : Rat) / 20480000000), D0 := ((49669020967 : Rat) / 20480000000), D1 := ((12447130919 : Rat) / 20480000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((10835144503348214359 : Rat) / 50000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((402422170415917 : Rat) / 2000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49669020967 : Rat) / 20480000000), R := ((24838212783 : Rat) / 10240000000), D0 := ((24838212783 : Rat) / 10240000000), D1 := ((6227267759 : Rat) / 10240000000), D2 := ((2717487833 : Rat) / 20480000000), D3 := ((10817066869070870609 : Rat) / 50000000000000000000), D4 := ((14369816423828121 : Rat) / 40000000000000000), LB := ((9974079282955989 : Rat) / 50000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24838212783 : Rat) / 10240000000), R := ((9936766033 : Rat) / 4096000000), D0 := ((9936766033 : Rat) / 4096000000), D1 := ((12461940117 : Rat) / 20480000000), D2 := ((1355041617 : Rat) / 10240000000), D3 := ((10798989234793526859 : Rat) / 50000000000000000000), D4 := ((7177677158203123 : Rat) / 20000000000000000), LB := ((3978421587423897 : Rat) / 20000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9936766033 : Rat) / 4096000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((540535727 : Rat) / 4096000000), D3 := ((10780911600516183109 : Rat) / 50000000000000000000), D4 := ((14340892208984371 : Rat) / 40000000000000000), LB := ((19953214035269007 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((49698639363 : Rat) / 20480000000), D0 := ((49698639363 : Rat) / 20480000000), D1 := ((2495349863 : Rat) / 4096000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((10762833966238839359 : Rat) / 50000000000000000000), D4 := ((111925235168457 : Rat) / 312500000000000), LB := ((1258233483022661 : Rat) / 6250000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49698639363 : Rat) / 20480000000), R := ((24853021981 : Rat) / 10240000000), D0 := ((24853021981 : Rat) / 10240000000), D1 := ((6242076957 : Rat) / 10240000000), D2 := ((2687869437 : Rat) / 20480000000), D3 := ((10744756331961495609 : Rat) / 50000000000000000000), D4 := ((14311967994140621 : Rat) / 40000000000000000), LB := ((5106983340078669 : Rat) / 25000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24853021981 : Rat) / 10240000000), R := ((49713448561 : Rat) / 20480000000), D0 := ((49713448561 : Rat) / 20480000000), D1 := ((12491558513 : Rat) / 20480000000), D2 := ((1340232419 : Rat) / 10240000000), D3 := ((10726678697684151859 : Rat) / 50000000000000000000), D4 := ((7148752943359373 : Rat) / 20000000000000000), LB := ((4168413752136113 : Rat) / 20000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49713448561 : Rat) / 20480000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((2673060239 : Rat) / 20480000000), D3 := ((10708601063406808109 : Rat) / 50000000000000000000), D4 := ((14283043779296871 : Rat) / 40000000000000000), LB := ((10687202626891157 : Rat) / 50000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((49728257759 : Rat) / 20480000000), D0 := ((49728257759 : Rat) / 20480000000), D1 := ((12506367711 : Rat) / 20480000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((10690523429129464359 : Rat) / 50000000000000000000), D4 := ((3567145417968749 : Rat) / 10000000000000000), LB := ((5506301917074241 : Rat) / 25000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49728257759 : Rat) / 20480000000), R := ((24867831179 : Rat) / 10240000000), D0 := ((24867831179 : Rat) / 10240000000), D1 := ((1251377231 : Rat) / 2048000000), D2 := ((2658251041 : Rat) / 20480000000), D3 := ((10672445794852120609 : Rat) / 50000000000000000000), D4 := ((14254119564453121 : Rat) / 40000000000000000), LB := ((11130245286529 : Rat) / 48828125000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24867831179 : Rat) / 10240000000), R := ((49743066957 : Rat) / 20480000000), D0 := ((49743066957 : Rat) / 20480000000), D1 := ((12521176909 : Rat) / 20480000000), D2 := ((1325423221 : Rat) / 10240000000), D3 := ((10654368160574776859 : Rat) / 50000000000000000000), D4 := ((7119828728515623 : Rat) / 20000000000000000), LB := ((185025602775701 : Rat) / 781250000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49743066957 : Rat) / 20480000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((2643441843 : Rat) / 20480000000), D3 := ((10636290526297433109 : Rat) / 50000000000000000000), D4 := ((14225195349609371 : Rat) / 40000000000000000), LB := ((24691081493269373 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((9951575231 : Rat) / 4096000000), D0 := ((9951575231 : Rat) / 4096000000), D1 := ((12535986107 : Rat) / 20480000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((10618212892020089359 : Rat) / 50000000000000000000), D4 := ((1776341655273437 : Rat) / 5000000000000000), LB := ((1290921315139429 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9951575231 : Rat) / 4096000000), R := ((24882640377 : Rat) / 10240000000), D0 := ((24882640377 : Rat) / 10240000000), D1 := ((6271695353 : Rat) / 10240000000), D2 := ((525726529 : Rat) / 4096000000), D3 := ((10600135257742745609 : Rat) / 50000000000000000000), D4 := ((14196271134765621 : Rat) / 40000000000000000), LB := ((27065584079277727 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24882640377 : Rat) / 10240000000), R := ((49772685353 : Rat) / 20480000000), D0 := ((49772685353 : Rat) / 20480000000), D1 := ((2510159061 : Rat) / 4096000000), D2 := ((1310614023 : Rat) / 10240000000), D3 := ((10582057623465401859 : Rat) / 50000000000000000000), D4 := ((7090904513671873 : Rat) / 20000000000000000), LB := ((7108207220151569 : Rat) / 25000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49772685353 : Rat) / 20480000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((2613823447 : Rat) / 20480000000), D3 := ((10563979989188058109 : Rat) / 50000000000000000000), D4 := ((14167346919921871 : Rat) / 40000000000000000), LB := ((5984087267582039 : Rat) / 20000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((49787494551 : Rat) / 20480000000), D0 := ((49787494551 : Rat) / 20480000000), D1 := ((12565604503 : Rat) / 20480000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((10545902354910714359 : Rat) / 50000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((3152868366514683 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49787494551 : Rat) / 20480000000), R := ((995897983 : Rat) / 409600000), D0 := ((995897983 : Rat) / 409600000), D1 := ((6286504551 : Rat) / 10240000000), D2 := ((2599014249 : Rat) / 20480000000), D3 := ((10527824720633370609 : Rat) / 50000000000000000000), D4 := ((14138422705078121 : Rat) / 40000000000000000), LB := ((33257849669598993 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((995897983 : Rat) / 409600000), R := ((49802303749 : Rat) / 20480000000), D0 := ((49802303749 : Rat) / 20480000000), D1 := ((12580413701 : Rat) / 20480000000), D2 := ((51832193 : Rat) / 409600000), D3 := ((10509747086356026859 : Rat) / 50000000000000000000), D4 := ((7061980298828123 : Rat) / 20000000000000000), LB := ((3510821476223197 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49802303749 : Rat) / 20480000000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((2584205051 : Rat) / 20480000000), D3 := ((10491669452078683109 : Rat) / 50000000000000000000), D4 := ((14109498490234371 : Rat) / 40000000000000000), LB := ((37080060967864537 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((49817112947 : Rat) / 20480000000), D0 := ((49817112947 : Rat) / 20480000000), D1 := ((12595222899 : Rat) / 20480000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((10473591817801339359 : Rat) / 50000000000000000000), D4 := ((880939773925781 : Rat) / 2500000000000000), LB := ((1958683596795241 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49817112947 : Rat) / 20480000000), R := ((24912258773 : Rat) / 10240000000), D0 := ((24912258773 : Rat) / 10240000000), D1 := ((6301313749 : Rat) / 10240000000), D2 := ((2569395853 : Rat) / 20480000000), D3 := ((10455514183523995609 : Rat) / 50000000000000000000), D4 := ((14080574275390621 : Rat) / 40000000000000000), LB := ((41389332950837743 : Rat) / 100000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24912258773 : Rat) / 10240000000), R := ((9966384429 : Rat) / 4096000000), D0 := ((9966384429 : Rat) / 4096000000), D1 := ((12610032097 : Rat) / 20480000000), D2 := ((1280995627 : Rat) / 10240000000), D3 := ((10437436549246651859 : Rat) / 50000000000000000000), D4 := ((7033056083984373 : Rat) / 20000000000000000), LB := ((4372733094269443 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9966384429 : Rat) / 4096000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((510917331 : Rat) / 4096000000), D3 := ((10419358914969308109 : Rat) / 50000000000000000000), D4 := ((14051650060546871 : Rat) / 40000000000000000), LB := ((1154698862458163 : Rat) / 2500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((49846731343 : Rat) / 20480000000), D0 := ((49846731343 : Rat) / 20480000000), D1 := ((2524968259 : Rat) / 4096000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10401281280691964359 : Rat) / 50000000000000000000), D4 := ((3509296988281249 : Rat) / 10000000000000000), LB := ((4877149387175067 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49846731343 : Rat) / 20480000000), R := ((24927067971 : Rat) / 10240000000), D0 := ((24927067971 : Rat) / 10240000000), D1 := ((6316122947 : Rat) / 10240000000), D2 := ((2539777457 : Rat) / 20480000000), D3 := ((10383203646414620609 : Rat) / 50000000000000000000), D4 := ((14022725845703121 : Rat) / 40000000000000000), LB := ((514782409954187 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24927067971 : Rat) / 10240000000), R := ((49861540541 : Rat) / 20480000000), D0 := ((49861540541 : Rat) / 20480000000), D1 := ((12639650493 : Rat) / 20480000000), D2 := ((1266186429 : Rat) / 10240000000), D3 := ((10365126012137276859 : Rat) / 50000000000000000000), D4 := ((7004131869140623 : Rat) / 20000000000000000), LB := ((5430848949102701 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49861540541 : Rat) / 20480000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((2524968259 : Rat) / 20480000000), D3 := ((10347048377859933109 : Rat) / 50000000000000000000), D4 := ((13993801630859371 : Rat) / 40000000000000000), LB := ((2863126734055921 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((24941877169 : Rat) / 10240000000), D0 := ((24941877169 : Rat) / 10240000000), D1 := ((1266186429 : Rat) / 2048000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((10328970743582589359 : Rat) / 50000000000000000000), D4 := ((1747417440429687 : Rat) / 5000000000000000), LB := ((24085269903747 : Rat) / 625000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24941877169 : Rat) / 10240000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((1251377231 : Rat) / 10240000000), D3 := ((10292815475027901859 : Rat) / 50000000000000000000), D4 := ((6975207654296873 : Rat) / 20000000000000000), LB := ((2087293339787799 : Rat) / 20000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((24956686367 : Rat) / 10240000000), D0 := ((24956686367 : Rat) / 10240000000), D1 := ((6345741343 : Rat) / 10240000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10256660206473214359 : Rat) / 50000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((1751915662307757 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24956686367 : Rat) / 10240000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((1236568033 : Rat) / 10240000000), D3 := ((10220504937918526859 : Rat) / 50000000000000000000), D4 := ((6946283439453123 : Rat) / 20000000000000000), LB := ((1255207621251933 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((4994299113 : Rat) / 2048000000), D0 := ((4994299113 : Rat) / 2048000000), D1 := ((6360550541 : Rat) / 10240000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((10184349669363839359 : Rat) / 50000000000000000000), D4 := ((433238833251953 : Rat) / 1250000000000000), LB := ((16596961037043667 : Rat) / 50000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4994299113 : Rat) / 2048000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((244351767 : Rat) / 2048000000), D3 := ((10148194400809151859 : Rat) / 50000000000000000000), D4 := ((6917359224609373 : Rat) / 20000000000000000), LB := ((10447740606419481 : Rat) / 25000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((24986304763 : Rat) / 10240000000), D0 := ((24986304763 : Rat) / 10240000000), D1 := ((6375359739 : Rat) / 10240000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10112039132254464359 : Rat) / 50000000000000000000), D4 := ((3451448558593749 : Rat) / 10000000000000000), LB := ((1272444990324563 : Rat) / 2500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24986304763 : Rat) / 10240000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((1206949637 : Rat) / 10240000000), D3 := ((10075883863699776859 : Rat) / 50000000000000000000), D4 := ((6888435009765623 : Rat) / 20000000000000000), LB := ((6051698944519041 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((25001113961 : Rat) / 10240000000), D0 := ((25001113961 : Rat) / 10240000000), D1 := ((6390168937 : Rat) / 10240000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((10039728595145089359 : Rat) / 50000000000000000000), D4 := ((1718493225585937 : Rat) / 5000000000000000), LB := ((7065111781328487 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25001113961 : Rat) / 10240000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((1192140439 : Rat) / 10240000000), D3 := ((10003573326590401859 : Rat) / 50000000000000000000), D4 := ((6859510794921873 : Rat) / 20000000000000000), LB := ((4065140055162647 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((25015923159 : Rat) / 10240000000), D0 := ((25015923159 : Rat) / 10240000000), D1 := ((1280995627 : Rat) / 2048000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((9967418058035714359 : Rat) / 50000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((4623734330830853 : Rat) / 5000000000000000000) }
]

def block412RightChunk000L : Rat := ((86836859375000000177 : Rat) / 50000000000000000000)
def block412RightChunk000R : Rat := ((25015923159 : Rat) / 10240000000)

def block412RightChunk000Certificate : Bool :=
  allBoxesValid block412RightChunk000 &&
  coversFromBool block412RightChunk000 block412RightChunk000L block412RightChunk000R

theorem block412RightChunk000Certificate_eq_true :
    block412RightChunk000Certificate = true := by
  native_decide

def block412RightChunk001 : List RatBox := [
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25015923159 : Rat) / 10240000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((1177331241 : Rat) / 10240000000), D3 := ((9931262789481026859 : Rat) / 50000000000000000000), D4 := ((6830586580078123 : Rat) / 20000000000000000), LB := ((5208472649924009 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((9895107520926339359 : Rat) / 50000000000000000000), D4 := ((852015559082031 : Rat) / 2500000000000000), LB := ((11879430615709119 : Rat) / 250000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((9822796983816964359 : Rat) / 50000000000000000000), D4 := ((3393600128906249 : Rat) / 10000000000000000), LB := ((1239460169422113 : Rat) / 4000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((9750486446707589359 : Rat) / 50000000000000000000), D4 := ((1689569010742187 : Rat) / 5000000000000000), LB := ((1483901343545327 : Rat) / 2500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((9678175909598214359 : Rat) / 50000000000000000000), D4 := ((3364675914062499 : Rat) / 10000000000000000), LB := ((1123541257336217 : Rat) / 1250000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((501651291 : Rat) / 204800000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 204800000), D3 := ((9605865372488839359 : Rat) / 50000000000000000000), D4 := ((209388362915039 : Rat) / 625000000000000), LB := ((2451833554703603 : Rat) / 2000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((9533554835379464359 : Rat) / 50000000000000000000), D4 := ((3335751699218749 : Rat) / 10000000000000000), LB := ((3150103746295263 : Rat) / 2000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((9461244298270089359 : Rat) / 50000000000000000000), D4 := ((1660644795898437 : Rat) / 5000000000000000), LB := ((973242086240729 : Rat) / 500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9388933761160714359 : Rat) / 50000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((6960666716453179 : Rat) / 50000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9244312686941964359 : Rat) / 50000000000000000000), D4 := ((3277903269531249 : Rat) / 10000000000000000), LB := ((627391443029637 : Rat) / 625000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9099691612723214359 : Rat) / 50000000000000000000), D4 := ((3248979054687499 : Rat) / 10000000000000000), LB := ((980875291753211 : Rat) / 500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((8955070538504464359 : Rat) / 50000000000000000000), D4 := ((3220054839843749 : Rat) / 10000000000000000), LB := ((30152386496001687 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((8810449464285714359 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((8333317095861853 : Rat) / 2000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((8665828390066964359 : Rat) / 50000000000000000000), D4 := ((3162206410156249 : Rat) / 10000000000000000), LB := ((677312659233641 : Rat) / 125000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((632617563 : Rat) / 256000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((8521207315848214359 : Rat) / 50000000000000000000), D4 := ((3133282195312499 : Rat) / 10000000000000000), LB := ((4951699353744149 : Rat) / 2000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8231965167410714359 : Rat) / 50000000000000000000), D4 := ((3075433765624999 : Rat) / 10000000000000000), LB := ((5535948143384789 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((7942723018973214359 : Rat) / 50000000000000000000), D4 := ((3017585335937499 : Rat) / 10000000000000000), LB := ((2260720973487937 : Rat) / 250000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((7653480870535714359 : Rat) / 50000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((4648280019321729 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7074996573660714359 : Rat) / 50000000000000000000), D4 := ((2844040046874999 : Rat) / 10000000000000000), LB := ((7132476490974267 : Rat) / 500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6496512276785714359 : Rat) / 50000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((10031413059909927 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5339543683035714359 : Rat) / 50000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((4275400326530951 : Rat) / 100000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((132079325089285714359 : Rat) / 50000000000000000000), D0 := ((132079325089285714359 : Rat) / 50000000000000000000), D1 := ((41205570089285714359 : Rat) / 50000000000000000000), D2 := ((4182575089285714359 : Rat) / 50000000000000000000), D3 := ((4182575089285714359 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((13421081800720963 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((132079325089285714359 : Rat) / 50000000000000000000), R := ((268925959017857143107 : Rat) / 100000000000000000000), D0 := ((268925959017857143107 : Rat) / 100000000000000000000), D1 := ((87178449017857143107 : Rat) / 100000000000000000000), D2 := ((13132459017857143107 : Rat) / 100000000000000000000), D3 := ((4767308839285714389 : Rat) / 100000000000000000000), D4 := ((7145203660714280641 : Rat) / 50000000000000000000), LB := ((3170120473492879 : Rat) / 20000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((268925959017857143107 : Rat) / 100000000000000000000), R := ((542619226875000000603 : Rat) / 200000000000000000000), D0 := ((542619226875000000603 : Rat) / 200000000000000000000), D1 := ((179124206875000000603 : Rat) / 200000000000000000000), D2 := ((31032226875000000603 : Rat) / 200000000000000000000), D3 := ((14301926517857143167 : Rat) / 200000000000000000000), D4 := ((9523098482142846893 : Rat) / 100000000000000000000), LB := ((4957210598852421 : Rat) / 100000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((542619226875000000603 : Rat) / 200000000000000000000), R := ((218001152517857143119 : Rat) / 80000000000000000000), D0 := ((218001152517857143119 : Rat) / 80000000000000000000), D1 := ((72603144517857143119 : Rat) / 80000000000000000000), D2 := ((13366352517857143119 : Rat) / 80000000000000000000), D3 := ((33371161875000000723 : Rat) / 400000000000000000000), D4 := ((14278888124999979397 : Rat) / 200000000000000000000), LB := ((8443066766739213 : Rat) / 500000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((218001152517857143119 : Rat) / 80000000000000000000), R := ((2184778834017857145579 : Rat) / 800000000000000000000), D0 := ((2184778834017857145579 : Rat) / 800000000000000000000), D1 := ((730798754017857145579 : Rat) / 800000000000000000000), D2 := ((138430834017857145579 : Rat) / 800000000000000000000), D3 := ((14301926517857143167 : Rat) / 160000000000000000000), D4 := ((4758093482142848881 : Rat) / 80000000000000000000), LB := ((198474560897631 : Rat) / 31250000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2184778834017857145579 : Rat) / 800000000000000000000), R := ((4374324976875000005547 : Rat) / 1600000000000000000000), D0 := ((4374324976875000005547 : Rat) / 1600000000000000000000), D1 := ((1466364816875000005547 : Rat) / 1600000000000000000000), D2 := ((281628976875000005547 : Rat) / 1600000000000000000000), D3 := ((147786574017857146059 : Rat) / 1600000000000000000000), D4 := ((42813625982142774421 : Rat) / 800000000000000000000), LB := ((5706649992093027 : Rat) / 2000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4374324976875000005547 : Rat) / 1600000000000000000000), R := ((8753417262589285725483 : Rat) / 3200000000000000000000), D0 := ((8753417262589285725483 : Rat) / 3200000000000000000000), D1 := ((2937496942589285725483 : Rat) / 3200000000000000000000), D2 := ((568025262589285725483 : Rat) / 3200000000000000000000), D3 := ((300340456875000006507 : Rat) / 3200000000000000000000), D4 := ((80859943124999834453 : Rat) / 1600000000000000000000), LB := ((8101773737318463 : Rat) / 5000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8753417262589285725483 : Rat) / 3200000000000000000000), R := ((3502320366803571433071 : Rat) / 1280000000000000000000), D0 := ((3502320366803571433071 : Rat) / 1280000000000000000000), D1 := ((1175952238803571433071 : Rat) / 1280000000000000000000), D2 := ((228163566803571433071 : Rat) / 1280000000000000000000), D3 := ((605448222589285727403 : Rat) / 6400000000000000000000), D4 := ((156952577410713954517 : Rat) / 3200000000000000000000), LB := ((11455734697137787 : Rat) / 10000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3502320366803571433071 : Rat) / 1280000000000000000000), R := ((35027970976875000045099 : Rat) / 12800000000000000000000), D0 := ((35027970976875000045099 : Rat) / 12800000000000000000000), D1 := ((11764289696875000045099 : Rat) / 12800000000000000000000), D2 := ((2286402976875000045099 : Rat) / 12800000000000000000000), D3 := ((243132750803571433839 : Rat) / 2560000000000000000000), D4 := ((61827569196428438929 : Rat) / 1280000000000000000000), LB := ((945496891265607 : Rat) / 1000000000000000000) },
  { w1 := ((1779684339050101 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((14416667448164183 : Rat) / 50000000000000000), w4 := ((2217630640861673 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132079325089285714359 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35027970976875000045099 : Rat) / 12800000000000000000000), R := ((34211658482142857187 : Rat) / 12500000000000000000), D0 := ((34211658482142857187 : Rat) / 12500000000000000000), D1 := ((11493219732142857187 : Rat) / 12500000000000000000), D2 := ((2237470982142857187 : Rat) / 12500000000000000000), D3 := ((4767308839285714389 : Rat) / 50000000000000000000), D4 := ((613508383124998674901 : Rat) / 12800000000000000000000), LB := ((7910598664101487 : Rat) / 100000000000000000000) }
]

def block412RightChunk001L : Rat := ((25015923159 : Rat) / 10240000000)
def block412RightChunk001R : Rat := ((34211658482142857187 : Rat) / 12500000000000000000)

def block412RightChunk001Certificate : Bool :=
  allBoxesValid block412RightChunk001 &&
  coversFromBool block412RightChunk001 block412RightChunk001L block412RightChunk001R

theorem block412RightChunk001Certificate_eq_true :
    block412RightChunk001Certificate = true := by
  native_decide

def block412RightChainCertificate : Bool :=
  decide (
    block412RightL = ((86836859375000000177 : Rat) / 50000000000000000000) /\
    ((25015923159 : Rat) / 10240000000) = ((25015923159 : Rat) / 10240000000) /\
    ((34211658482142857187 : Rat) / 12500000000000000000) = block412RightR)

theorem block412RightChainCertificate_eq_true :
    block412RightChainCertificate = true := by
  native_decide

def block412LeftBoxCount : Nat := boxCount block412LeftBoxes
def block412RightBoxCount : Nat := 131

def block412_rational_certificate : Prop :=
    block412LeftCertificate = true /\
    block412RightChainCertificate = true /\
    block412RightChunk000Certificate = true /\
    block412RightChunk001Certificate = true

theorem block412_rational_certificate_proof :
    block412_rational_certificate := by
  exact ⟨block412LeftCertificate_eq_true, block412RightChainCertificate_eq_true, block412RightChunk000Certificate_eq_true, block412RightChunk001Certificate_eq_true⟩

end Block412
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block412

open Set

def block412W1 : Rat := ((1779684339050101 : Rat) / 2500000000000000)
def block412W2 : Rat := (0 : Rat)
def block412W3 : Rat := ((14416667448164183 : Rat) / 50000000000000000)
def block412W4 : Rat := ((2217630640861673 : Rat) / 25000000000000000)
def block412S1 : Rat := ((18174751 : Rat) / 10000000)
def block412S2 : Rat := ((511587 : Rat) / 200000)
def block412S3 : Rat := ((132079325089285714359 : Rat) / 50000000000000000000)
def block412S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block412V (y : ℝ) : ℝ :=
  ratPotential block412W1 block412W2 block412W3 block412W4 block412S1 block412S2 block412S3 block412S4 y

def block412LeftParamsCertificate : Bool :=
  allBoxesSameParams block412LeftBoxes block412W1 block412W2 block412W3 block412W4 block412S1 block412S2 block412S3 block412S4

theorem block412LeftParamsCertificate_eq_true :
    block412LeftParamsCertificate = true := by
  native_decide

theorem block412_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block412LeftL : ℝ) (block412LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block412S1 : ℝ))
    (hy2ne : y ≠ (block412S2 : ℝ))
    (hy3ne : y ≠ (block412S3 : ℝ))
    (hy4ne : y ≠ (block412S4 : ℝ)) :
    0 < block412V y := by
  have hcert := block412LeftCertificate_eq_true
  unfold block412LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block412LeftBoxes) (lo := block412LeftL) (hi := block412LeftR)
    (w1 := block412W1) (w2 := block412W2) (w3 := block412W3) (w4 := block412W4)
    (s1 := block412S1) (s2 := block412S2) (s3 := block412S3) (s4 := block412S4)
    hboxes hcover block412LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block412RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block412RightChunk000 block412W1 block412W2 block412W3 block412W4 block412S1 block412S2 block412S3 block412S4

theorem block412RightChunk000ParamsCertificate_eq_true :
    block412RightChunk000ParamsCertificate = true := by
  native_decide

theorem block412_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block412RightChunk000L : ℝ) (block412RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block412S1 : ℝ))
    (hy2ne : y ≠ (block412S2 : ℝ))
    (hy3ne : y ≠ (block412S3 : ℝ))
    (hy4ne : y ≠ (block412S4 : ℝ)) :
    0 < block412V y := by
  have hcert := block412RightChunk000Certificate_eq_true
  unfold block412RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block412RightChunk000) (lo := block412RightChunk000L) (hi := block412RightChunk000R)
    (w1 := block412W1) (w2 := block412W2) (w3 := block412W3) (w4 := block412W4)
    (s1 := block412S1) (s2 := block412S2) (s3 := block412S3) (s4 := block412S4)
    hboxes hcover block412RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block412RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block412RightChunk001 block412W1 block412W2 block412W3 block412W4 block412S1 block412S2 block412S3 block412S4

theorem block412RightChunk001ParamsCertificate_eq_true :
    block412RightChunk001ParamsCertificate = true := by
  native_decide

theorem block412_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block412RightChunk001L : ℝ) (block412RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block412S1 : ℝ))
    (hy2ne : y ≠ (block412S2 : ℝ))
    (hy3ne : y ≠ (block412S3 : ℝ))
    (hy4ne : y ≠ (block412S4 : ℝ)) :
    0 < block412V y := by
  have hcert := block412RightChunk001Certificate_eq_true
  unfold block412RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block412RightChunk001) (lo := block412RightChunk001L) (hi := block412RightChunk001R)
    (w1 := block412W1) (w2 := block412W2) (w3 := block412W3) (w4 := block412W4)
    (s1 := block412S1) (s2 := block412S2) (s3 := block412S3) (s4 := block412S4)
    hboxes hcover block412RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block412_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block412RightL : ℝ) (block412RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block412S1 : ℝ))
    (hy2ne : y ≠ (block412S2 : ℝ))
    (hy3ne : y ≠ (block412S3 : ℝ))
    (hy4ne : y ≠ (block412S4 : ℝ)) :
    0 < block412V y := by
  by_cases h0 : y ≤ (block412RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block412RightChunk000L : ℝ) (block412RightChunk000R : ℝ) := by
      have hL : (block412RightChunk000L : ℝ) = (block412RightL : ℝ) := by
        norm_num [block412RightChunk000L, block412RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block412_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block412RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block412RightChunk001L : ℝ) = (block412RightChunk000R : ℝ) := by
      norm_num [block412RightChunk001L, block412RightChunk000R]
    have hR : (block412RightChunk001R : ℝ) = (block412RightR : ℝ) := by
      norm_num [block412RightChunk001R, block412RightR]
    have hyc : y ∈ Icc (block412RightChunk001L : ℝ) (block412RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block412_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block412_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block412LeftL : ℝ) (block412LeftR : ℝ) →
    y ≠ 0 → y ≠ (block412S1 : ℝ) → y ≠ (block412S2 : ℝ) →
    y ≠ (block412S3 : ℝ) → y ≠ (block412S4 : ℝ) → 0 < block412V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block412RightL : ℝ) (block412RightR : ℝ) →
    y ≠ 0 → y ≠ (block412S1 : ℝ) → y ≠ (block412S2 : ℝ) →
    y ≠ (block412S3 : ℝ) → y ≠ (block412S4 : ℝ) → 0 < block412V y)

theorem block412_reallog_certificate_proof :
    block412_reallog_certificate := by
  exact ⟨block412_left_V_pos, block412_right_V_pos⟩

end Block412
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block412.block412V
#check Erdos1038Lean.M1817475.Block412.block412_left_V_pos
#check Erdos1038Lean.M1817475.Block412.block412_right_V_pos
#check Erdos1038Lean.M1817475.Block412.block412_reallog_certificate_proof
