/-
Self-contained Lean4Web paste file.
Block 352 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block352

def block352LeftL : Rat := ((37423332589285714437 : Rat) / 50000000000000000000)
def block352LeftR : Rat := ((1169784598214285719 : Rat) / 1562500000000000000)
def block352RightL : Rat := ((87423332589285714437 : Rat) / 50000000000000000000)
def block352RightR : Rat := ((4294784598214285719 : Rat) / 1562500000000000000)

def block352LeftBoxes : List RatBox := [
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37423332589285714437 : Rat) / 50000000000000000000), R := ((1169784598214285719 : Rat) / 1562500000000000000), D0 := ((1169784598214285719 : Rat) / 1562500000000000000), D1 := ((53450422410714285563 : Rat) / 50000000000000000000), D2 := ((90473417410714285563 : Rat) / 50000000000000000000), D3 := ((47914469464285714221 : Rat) / 25000000000000000000), D4 := ((101195173839285709161 : Rat) / 50000000000000000000), LB := ((6226519846900161 : Rat) / 1000000000000000000) }
]

def block352LeftCertificate : Bool :=
  allBoxesValid block352LeftBoxes &&
  coversFromBool block352LeftBoxes block352LeftL block352LeftR

theorem block352LeftCertificate_eq_true :
    block352LeftCertificate = true := by
  native_decide

def block352RightChunk000 : List RatBox := [
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87423332589285714437 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3450422410714285563 : Rat) / 50000000000000000000), D2 := ((40473417410714285563 : Rat) / 50000000000000000000), D3 := ((22914469464285714221 : Rat) / 25000000000000000000), D4 := ((51195173839285709161 : Rat) / 50000000000000000000), LB := ((18350888856088907 : Rat) / 10000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42378516517857142879 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((15924359975633423 : Rat) / 100000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23867019017857142879 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((515466444083859 : Rat) / 5000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19239144642857142879 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((3336651996698301 : Rat) / 50000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16925207455357142879 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((200010350916259 : Rat) / 20000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14611270267857142879 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((2800637468956653 : Rat) / 250000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13454301674107142879 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((15446952081366927 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12875817377232142879 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((7539939992498773 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12297333080357142879 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((7127145850951977 : Rat) / 10000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11718848783482142879 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((5806536657896377 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11429606635044642879 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((33488817633457457 : Rat) / 10000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11140364486607142879 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((1523510583399737 : Rat) / 1250000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10851122338169642879 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((2361649305630653 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10706501263950892879 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((1972305983303363 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10561880189732142879 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((3259135026657617 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10417259115513392879 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((1334803487609601 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10272638041294642879 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((21789764202017337 : Rat) / 10000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10128016967075892879 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((3580847299749279 : Rat) / 2000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9983395892857142879 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((3768465381326011 : Rat) / 2500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9838774818638392879 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((666794003359103 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9694153744419642879 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((12730738871249703 : Rat) / 10000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9549532670200892879 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((2660497212776447 : Rat) / 2000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9404911595982142879 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((3019846674541693 : Rat) / 2000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9260290521763392879 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((908684974425783 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9115669447544642879 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((5645963166625509 : Rat) / 2500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8971048373325892879 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((2839367560698719 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8826427299107142879 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((35674082207411417 : Rat) / 10000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8681806224888392879 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((4450402455710711 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8537185150669642879 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((5074896634351123 : Rat) / 10000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8247943002232142879 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((6336839069500333 : Rat) / 2000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7958700853794642879 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((13243659443456901 : Rat) / 2000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7669458705357142879 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((1272618811291537 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7090974408482142879 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((3421668434851921 : Rat) / 250000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6512490111607142879 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((7248408419319563 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516942521517857142879 : Rat) / 200000000000000000000), D0 := ((516942521517857142879 : Rat) / 200000000000000000000), D1 := ((153447501517857142879 : Rat) / 200000000000000000000), D2 := ((5355521517857142879 : Rat) / 200000000000000000000), D3 := ((5355521517857142879 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((1707655279975251 : Rat) / 200000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516942521517857142879 : Rat) / 200000000000000000000), R := ((1039240564553571428637 : Rat) / 400000000000000000000), D0 := ((1039240564553571428637 : Rat) / 400000000000000000000), D1 := ((312250524553571428637 : Rat) / 400000000000000000000), D2 := ((16066564553571428637 : Rat) / 400000000000000000000), D3 := ((16066564553571428637 : Rat) / 200000000000000000000), D4 := ((37531504196428551513 : Rat) / 200000000000000000000), LB := ((15010671972877643 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1039240564553571428637 : Rat) / 400000000000000000000), R := ((261149021517857142879 : Rat) / 100000000000000000000), D0 := ((261149021517857142879 : Rat) / 100000000000000000000), D1 := ((79401511517857142879 : Rat) / 100000000000000000000), D2 := ((5355521517857142879 : Rat) / 100000000000000000000), D3 := ((5355521517857142879 : Rat) / 80000000000000000000), D4 := ((69707486874999960147 : Rat) / 400000000000000000000), LB := ((835152856776309 : Rat) / 25000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261149021517857142879 : Rat) / 100000000000000000000), R := ((527653564553571428637 : Rat) / 200000000000000000000), D0 := ((527653564553571428637 : Rat) / 200000000000000000000), D1 := ((164158544553571428637 : Rat) / 200000000000000000000), D2 := ((16066564553571428637 : Rat) / 200000000000000000000), D3 := ((5355521517857142879 : Rat) / 100000000000000000000), D4 := ((16087991339285704317 : Rat) / 100000000000000000000), LB := ((9241305441358927 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((527653564553571428637 : Rat) / 200000000000000000000), R := ((133252271517857142879 : Rat) / 50000000000000000000), D0 := ((133252271517857142879 : Rat) / 50000000000000000000), D1 := ((42378516517857142879 : Rat) / 50000000000000000000), D2 := ((5355521517857142879 : Rat) / 50000000000000000000), D3 := ((5355521517857142879 : Rat) / 200000000000000000000), D4 := ((5364092232142853151 : Rat) / 40000000000000000000), LB := ((4733183601293031 : Rat) / 50000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133252271517857142879 : Rat) / 50000000000000000000), R := ((107437984339285714329 : Rat) / 40000000000000000000), D0 := ((107437984339285714329 : Rat) / 40000000000000000000), D1 := ((34738980339285714329 : Rat) / 40000000000000000000), D2 := ((5120584339285714329 : Rat) / 40000000000000000000), D3 := ((4180835625000000129 : Rat) / 200000000000000000000), D4 := ((5366234910714280719 : Rat) / 50000000000000000000), LB := ((621358227837443 : Rat) / 5000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((107437984339285714329 : Rat) / 40000000000000000000), R := ((270685378660714285887 : Rat) / 100000000000000000000), D0 := ((270685378660714285887 : Rat) / 100000000000000000000), D1 := ((88937868660714285887 : Rat) / 100000000000000000000), D2 := ((14891878660714285887 : Rat) / 100000000000000000000), D3 := ((4180835625000000129 : Rat) / 100000000000000000000), D4 := ((17284104017857122747 : Rat) / 200000000000000000000), LB := ((14138797024523753 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((270685378660714285887 : Rat) / 100000000000000000000), R := ((1086922350267857143677 : Rat) / 400000000000000000000), D0 := ((1086922350267857143677 : Rat) / 400000000000000000000), D1 := ((359932310267857143677 : Rat) / 400000000000000000000), D2 := ((63748350267857143677 : Rat) / 400000000000000000000), D3 := ((4180835625000000129 : Rat) / 80000000000000000000), D4 := ((6551634196428561309 : Rat) / 100000000000000000000), LB := ((1449396748321341 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1086922350267857143677 : Rat) / 400000000000000000000), R := ((2178025536160714287483 : Rat) / 800000000000000000000), D0 := ((2178025536160714287483 : Rat) / 800000000000000000000), D1 := ((724045456160714287483 : Rat) / 800000000000000000000), D2 := ((131677536160714287483 : Rat) / 800000000000000000000), D3 := ((45989191875000001419 : Rat) / 800000000000000000000), D4 := ((22025701160714245107 : Rat) / 400000000000000000000), LB := ((25565391954620043 : Rat) / 10000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2178025536160714287483 : Rat) / 800000000000000000000), R := ((872046381589285715019 : Rat) / 320000000000000000000), D0 := ((872046381589285715019 : Rat) / 320000000000000000000), D1 := ((290454349589285715019 : Rat) / 320000000000000000000), D2 := ((53507181589285715019 : Rat) / 320000000000000000000), D3 := ((96159219375000002967 : Rat) / 1600000000000000000000), D4 := ((7974113339285698017 : Rat) / 160000000000000000000), LB := ((2696937203793437 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((872046381589285715019 : Rat) / 320000000000000000000), R := ((545551592946428571903 : Rat) / 200000000000000000000), D0 := ((545551592946428571903 : Rat) / 200000000000000000000), D1 := ((182056572946428571903 : Rat) / 200000000000000000000), D2 := ((33964592946428571903 : Rat) / 200000000000000000000), D3 := ((12542506875000000387 : Rat) / 200000000000000000000), D4 := ((75560297767856980041 : Rat) / 1600000000000000000000), LB := ((1367926252830963 : Rat) / 625000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545551592946428571903 : Rat) / 200000000000000000000), R := ((8733006322767857150577 : Rat) / 3200000000000000000000), D0 := ((8733006322767857150577 : Rat) / 3200000000000000000000), D1 := ((2917086002767857150577 : Rat) / 3200000000000000000000), D2 := ((547614322767857150577 : Rat) / 3200000000000000000000), D3 := ((204860945625000006321 : Rat) / 3200000000000000000000), D4 := ((8922432767857122489 : Rat) / 200000000000000000000), LB := ((4842089832154617 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8733006322767857150577 : Rat) / 3200000000000000000000), R := ((4368593579196428575353 : Rat) / 1600000000000000000000), D0 := ((4368593579196428575353 : Rat) / 1600000000000000000000), D1 := ((1460633419196428575353 : Rat) / 1600000000000000000000), D2 := ((275897579196428575353 : Rat) / 1600000000000000000000), D3 := ((4180835625000000129 : Rat) / 64000000000000000000), D4 := ((27715617732142791939 : Rat) / 640000000000000000000), LB := ((1519892288738367 : Rat) / 400000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4368593579196428575353 : Rat) / 1600000000000000000000), R := ((1748273598803571430167 : Rat) / 640000000000000000000), D0 := ((1748273598803571430167 : Rat) / 640000000000000000000), D1 := ((585089534803571430167 : Rat) / 640000000000000000000), D2 := ((111195198803571430167 : Rat) / 640000000000000000000), D3 := ((213222616875000006579 : Rat) / 3200000000000000000000), D4 := ((67198626517856979783 : Rat) / 1600000000000000000000), LB := ((1842515175310179 : Rat) / 625000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1748273598803571430167 : Rat) / 640000000000000000000), R := ((2186387207410714287741 : Rat) / 800000000000000000000), D0 := ((2186387207410714287741 : Rat) / 800000000000000000000), D1 := ((732407127410714287741 : Rat) / 800000000000000000000), D2 := ((140039207410714287741 : Rat) / 800000000000000000000), D3 := ((54350863125000001677 : Rat) / 800000000000000000000), D4 := ((130216417410713959437 : Rat) / 3200000000000000000000), LB := ((2292563607984577 : Rat) / 1000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2186387207410714287741 : Rat) / 800000000000000000000), R := ((8749729665267857151093 : Rat) / 3200000000000000000000), D0 := ((8749729665267857151093 : Rat) / 3200000000000000000000), D1 := ((2933809345267857151093 : Rat) / 3200000000000000000000), D2 := ((564337665267857151093 : Rat) / 3200000000000000000000), D3 := ((221584288125000006837 : Rat) / 3200000000000000000000), D4 := ((31508895446428489827 : Rat) / 800000000000000000000), LB := ((9199277598992417 : Rat) / 5000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8749729665267857151093 : Rat) / 3200000000000000000000), R := ((4376955250446428575611 : Rat) / 1600000000000000000000), D0 := ((4376955250446428575611 : Rat) / 1600000000000000000000), D1 := ((1468995090446428575611 : Rat) / 1600000000000000000000), D2 := ((284259250446428575611 : Rat) / 1600000000000000000000), D3 := ((112882561875000003483 : Rat) / 1600000000000000000000), D4 := ((121854746160713959179 : Rat) / 3200000000000000000000), LB := ((1996769826060063 : Rat) / 1250000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4376955250446428575611 : Rat) / 1600000000000000000000), R := ((8758091336517857151351 : Rat) / 3200000000000000000000), D0 := ((8758091336517857151351 : Rat) / 3200000000000000000000), D1 := ((2942171016517857151351 : Rat) / 3200000000000000000000), D2 := ((572699336517857151351 : Rat) / 3200000000000000000000), D3 := ((45989191875000001419 : Rat) / 640000000000000000000), D4 := ((2353478210714279181 : Rat) / 64000000000000000000), LB := ((3147768235347459 : Rat) / 2000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8758091336517857151351 : Rat) / 3200000000000000000000), R := ((219056804303571428787 : Rat) / 80000000000000000000), D0 := ((219056804303571428787 : Rat) / 80000000000000000000), D1 := ((73658796303571428787 : Rat) / 80000000000000000000), D2 := ((14422004303571428787 : Rat) / 80000000000000000000), D3 := ((29265849375000000903 : Rat) / 400000000000000000000), D4 := ((113493074910713958921 : Rat) / 3200000000000000000000), LB := ((17791612233896137 : Rat) / 10000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((219056804303571428787 : Rat) / 80000000000000000000), R := ((8766453007767857151609 : Rat) / 3200000000000000000000), D0 := ((8766453007767857151609 : Rat) / 3200000000000000000000), D1 := ((2950532687767857151609 : Rat) / 3200000000000000000000), D2 := ((581061007767857151609 : Rat) / 3200000000000000000000), D3 := ((238307630625000007353 : Rat) / 3200000000000000000000), D4 := ((13664029910714244849 : Rat) / 400000000000000000000), LB := ((4449151023329767 : Rat) / 2000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8766453007767857151609 : Rat) / 3200000000000000000000), R := ((4385316921696428575869 : Rat) / 1600000000000000000000), D0 := ((4385316921696428575869 : Rat) / 1600000000000000000000), D1 := ((1477356761696428575869 : Rat) / 1600000000000000000000), D2 := ((292620921696428575869 : Rat) / 1600000000000000000000), D3 := ((121244233125000003741 : Rat) / 1600000000000000000000), D4 := ((105131403660713958663 : Rat) / 3200000000000000000000), LB := ((1461541582036957 : Rat) / 500000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4385316921696428575869 : Rat) / 1600000000000000000000), R := ((8774814679017857151867 : Rat) / 3200000000000000000000), D0 := ((8774814679017857151867 : Rat) / 3200000000000000000000), D1 := ((2958894359017857151867 : Rat) / 3200000000000000000000), D2 := ((589422679017857151867 : Rat) / 3200000000000000000000), D3 := ((246669301875000007611 : Rat) / 3200000000000000000000), D4 := ((50475284017856979267 : Rat) / 1600000000000000000000), LB := ((7779022658258583 : Rat) / 2000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8774814679017857151867 : Rat) / 3200000000000000000000), R := ((2194748878660714287999 : Rat) / 800000000000000000000), D0 := ((2194748878660714287999 : Rat) / 800000000000000000000), D1 := ((740768798660714287999 : Rat) / 800000000000000000000), D2 := ((148400878660714287999 : Rat) / 800000000000000000000), D3 := ((12542506875000000387 : Rat) / 160000000000000000000), D4 := ((19353946482142791681 : Rat) / 640000000000000000000), LB := ((257042727089693 : Rat) / 50000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2194748878660714287999 : Rat) / 800000000000000000000), R := ((4393678592946428576127 : Rat) / 1600000000000000000000), D0 := ((4393678592946428576127 : Rat) / 1600000000000000000000), D1 := ((1485718432946428576127 : Rat) / 1600000000000000000000), D2 := ((300982592946428576127 : Rat) / 1600000000000000000000), D3 := ((129605904375000003999 : Rat) / 1600000000000000000000), D4 := ((23147224196428489569 : Rat) / 800000000000000000000), LB := ((4372896456306341 : Rat) / 2000000000000000000) },
  { w1 := ((9024572734552211 : Rat) / 10000000000000000), w2 := ((948893405498469 : Rat) / 20000000000000000), w3 := ((748122412504459 : Rat) / 5000000000000000), w4 := ((6917836042765413 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133252271517857142879 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4393678592946428576127 : Rat) / 1600000000000000000000), R := ((4294784598214285719 : Rat) / 1562500000000000000), D0 := ((4294784598214285719 : Rat) / 1562500000000000000), D1 := ((1454979754464285719 : Rat) / 1562500000000000000), D2 := ((298011160714285719 : Rat) / 1562500000000000000), D3 := ((4180835625000000129 : Rat) / 50000000000000000000), D4 := ((42113612767856979009 : Rat) / 1600000000000000000000), LB := ((3195050434196711 : Rat) / 500000000000000000) }
]

def block352RightChunk000L : Rat := ((87423332589285714437 : Rat) / 50000000000000000000)
def block352RightChunk000R : Rat := ((4294784598214285719 : Rat) / 1562500000000000000)

def block352RightChunk000Certificate : Bool :=
  allBoxesValid block352RightChunk000 &&
  coversFromBool block352RightChunk000 block352RightChunk000L block352RightChunk000R

theorem block352RightChunk000Certificate_eq_true :
    block352RightChunk000Certificate = true := by
  native_decide

def block352RightChainCertificate : Bool :=
  decide (
    block352RightL = ((87423332589285714437 : Rat) / 50000000000000000000) /\
    ((4294784598214285719 : Rat) / 1562500000000000000) = block352RightR)

theorem block352RightChainCertificate_eq_true :
    block352RightChainCertificate = true := by
  native_decide

def block352LeftBoxCount : Nat := boxCount block352LeftBoxes
def block352RightBoxCount : Nat := 59

def block352_rational_certificate : Prop :=
    block352LeftCertificate = true /\
    block352RightChainCertificate = true /\
    block352RightChunk000Certificate = true

theorem block352_rational_certificate_proof :
    block352_rational_certificate := by
  exact ⟨block352LeftCertificate_eq_true, block352RightChainCertificate_eq_true, block352RightChunk000Certificate_eq_true⟩

end Block352
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block352

open Set

def block352W1 : Rat := ((9024572734552211 : Rat) / 10000000000000000)
def block352W2 : Rat := ((948893405498469 : Rat) / 20000000000000000)
def block352W3 : Rat := ((748122412504459 : Rat) / 5000000000000000)
def block352W4 : Rat := ((6917836042765413 : Rat) / 50000000000000000)
def block352S1 : Rat := ((18174751 : Rat) / 10000000)
def block352S2 : Rat := ((511587 : Rat) / 200000)
def block352S3 : Rat := ((133252271517857142879 : Rat) / 50000000000000000000)
def block352S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block352V (y : ℝ) : ℝ :=
  ratPotential block352W1 block352W2 block352W3 block352W4 block352S1 block352S2 block352S3 block352S4 y

def block352LeftParamsCertificate : Bool :=
  allBoxesSameParams block352LeftBoxes block352W1 block352W2 block352W3 block352W4 block352S1 block352S2 block352S3 block352S4

theorem block352LeftParamsCertificate_eq_true :
    block352LeftParamsCertificate = true := by
  native_decide

theorem block352_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block352LeftL : ℝ) (block352LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block352S1 : ℝ))
    (hy2ne : y ≠ (block352S2 : ℝ))
    (hy3ne : y ≠ (block352S3 : ℝ))
    (hy4ne : y ≠ (block352S4 : ℝ)) :
    0 < block352V y := by
  have hcert := block352LeftCertificate_eq_true
  unfold block352LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block352LeftBoxes) (lo := block352LeftL) (hi := block352LeftR)
    (w1 := block352W1) (w2 := block352W2) (w3 := block352W3) (w4 := block352W4)
    (s1 := block352S1) (s2 := block352S2) (s3 := block352S3) (s4 := block352S4)
    hboxes hcover block352LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block352RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block352RightChunk000 block352W1 block352W2 block352W3 block352W4 block352S1 block352S2 block352S3 block352S4

theorem block352RightChunk000ParamsCertificate_eq_true :
    block352RightChunk000ParamsCertificate = true := by
  native_decide

theorem block352_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block352RightChunk000L : ℝ) (block352RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block352S1 : ℝ))
    (hy2ne : y ≠ (block352S2 : ℝ))
    (hy3ne : y ≠ (block352S3 : ℝ))
    (hy4ne : y ≠ (block352S4 : ℝ)) :
    0 < block352V y := by
  have hcert := block352RightChunk000Certificate_eq_true
  unfold block352RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block352RightChunk000) (lo := block352RightChunk000L) (hi := block352RightChunk000R)
    (w1 := block352W1) (w2 := block352W2) (w3 := block352W3) (w4 := block352W4)
    (s1 := block352S1) (s2 := block352S2) (s3 := block352S3) (s4 := block352S4)
    hboxes hcover block352RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block352_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block352RightL : ℝ) (block352RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block352S1 : ℝ))
    (hy2ne : y ≠ (block352S2 : ℝ))
    (hy3ne : y ≠ (block352S3 : ℝ))
    (hy4ne : y ≠ (block352S4 : ℝ)) :
    0 < block352V y := by
  have hL : (block352RightChunk000L : ℝ) = (block352RightL : ℝ) := by
    norm_num [block352RightChunk000L, block352RightL]
  have hR : (block352RightChunk000R : ℝ) = (block352RightR : ℝ) := by
    norm_num [block352RightChunk000R, block352RightR]
  have hyc : y ∈ Icc (block352RightChunk000L : ℝ) (block352RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block352_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block352_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block352LeftL : ℝ) (block352LeftR : ℝ) →
    y ≠ 0 → y ≠ (block352S1 : ℝ) → y ≠ (block352S2 : ℝ) →
    y ≠ (block352S3 : ℝ) → y ≠ (block352S4 : ℝ) → 0 < block352V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block352RightL : ℝ) (block352RightR : ℝ) →
    y ≠ 0 → y ≠ (block352S1 : ℝ) → y ≠ (block352S2 : ℝ) →
    y ≠ (block352S3 : ℝ) → y ≠ (block352S4 : ℝ) → 0 < block352V y)

theorem block352_reallog_certificate_proof :
    block352_reallog_certificate := by
  exact ⟨block352_left_V_pos, block352_right_V_pos⟩

end Block352
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block352.block352V
#check Erdos1038Lean.M1817475.Block352.block352_left_V_pos
#check Erdos1038Lean.M1817475.Block352.block352_right_V_pos
#check Erdos1038Lean.M1817475.Block352.block352_reallog_certificate_proof
