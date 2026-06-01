/-
Self-contained Lean4Web paste file.
Block 386 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block386

def block386LeftL : Rat := ((37090997767857143023 : Rat) / 50000000000000000000)
def block386LeftR : Rat := ((18550386160714285797 : Rat) / 25000000000000000000)
def block386RightL : Rat := ((87090997767857143023 : Rat) / 50000000000000000000)
def block386RightR : Rat := ((68550386160714285797 : Rat) / 25000000000000000000)

def block386LeftBoxes : List RatBox := [
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37090997767857143023 : Rat) / 50000000000000000000), R := ((18550386160714285797 : Rat) / 25000000000000000000), D0 := ((18550386160714285797 : Rat) / 25000000000000000000), D1 := ((53782757232142856977 : Rat) / 50000000000000000000), D2 := ((90805752232142856977 : Rat) / 50000000000000000000), D3 := ((23874151026785714257 : Rat) / 12500000000000000000), D4 := ((4061100346428571223 : Rat) / 2000000000000000000), LB := ((3150955320847963 : Rat) / 500000000000000000) }
]

def block386LeftCertificate : Bool :=
  allBoxesValid block386LeftBoxes &&
  coversFromBool block386LeftBoxes block386LeftL block386LeftR

theorem block386LeftCertificate_eq_true :
    block386LeftCertificate = true := by
  native_decide

def block386RightChunk000 : List RatBox := [
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87090997767857143023 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3782757232142856977 : Rat) / 50000000000000000000), D2 := ((40805752232142856977 : Rat) / 50000000000000000000), D3 := ((11374151026785714257 : Rat) / 12500000000000000000), D4 := ((2061100346428571223 : Rat) / 2000000000000000000), LB := ((15892184319930287 : Rat) / 10000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41713846875000000051 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((401460682239951 : Rat) / 4000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23202349375000000051 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((3332832050206979 : Rat) / 50000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18574475000000000051 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((248417094606843 : Rat) / 6250000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16260537812500000051 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((3617119004084039 : Rat) / 100000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((15103569218750000051 : Rat) / 50000000000000000000), D4 := ((10567236886160711799 : Rat) / 25000000000000000000), LB := ((14841797063539539 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13946600625000000051 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((1174892713398731 : Rat) / 62500000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((13368116328125000051 : Rat) / 50000000000000000000), D4 := ((9699510440848211799 : Rat) / 25000000000000000000), LB := ((2725813164026987 : Rat) / 250000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12789632031250000051 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((999561637427919 : Rat) / 250000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12211147734375000051 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((8638421153902981 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((123561673 : Rat) / 51200000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11921905585937500051 : Rat) / 50000000000000000000), D4 := ((8976405069754461799 : Rat) / 25000000000000000000), LB := ((3017536837227941 : Rat) / 500000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11632663437500000051 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((2324855832528689 : Rat) / 625000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11343421289062500051 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((3406514964594709 : Rat) / 2000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11054179140625000051 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((5116059866515477 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10909558066406250051 : Rat) / 50000000000000000000), D4 := ((8470231309988836799 : Rat) / 25000000000000000000), LB := ((4364239883396959 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10764936992187500051 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((7391048508464837 : Rat) / 2000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10620315917968750051 : Rat) / 50000000000000000000), D4 := ((8325610235770086799 : Rat) / 25000000000000000000), LB := ((15559408750742687 : Rat) / 5000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10475694843750000051 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((817315197008733 : Rat) / 312500000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10331073769531250051 : Rat) / 50000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((2208339535226339 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10186452695312500051 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((9465298412784373 : Rat) / 5000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10041831621093750051 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((1672118568228409 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9897210546875000051 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((1548245404559223 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9752589472656250051 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((15243665790622973 : Rat) / 10000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9607968398437500051 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((4009063675158367 : Rat) / 2500000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9463347324218750051 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((8947025125763397 : Rat) / 5000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9318726250000000051 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((4170707188178191 : Rat) / 2000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9174105175781250051 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((62385365376353 : Rat) / 25000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9029484101562500051 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((3023860888334867 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((8884863027343750051 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((3675334343078457 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8740241953125000051 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((4454892422114193 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((8595620878906250051 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((5368062492684317 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8450999804687500051 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((8164653410622641 : Rat) / 5000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8161757656250000051 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((2109387824120193 : Rat) / 500000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((7872515507812500051 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((3726321116030759 : Rat) / 500000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7583273359375000051 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((20840286004848163 : Rat) / 10000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7004789062500000051 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((3183805508580717 : Rat) / 250000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6426304765625000051 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((87453039375213 : Rat) / 3125000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5847820468750000051 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((2047973234967599 : Rat) / 62500000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516277851875000000051 : Rat) / 200000000000000000000), D0 := ((516277851875000000051 : Rat) / 200000000000000000000), D1 := ((152782831875000000051 : Rat) / 200000000000000000000), D2 := ((4690851875000000051 : Rat) / 200000000000000000000), D3 := ((4690851875000000051 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((2328751529176773 : Rat) / 50000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516277851875000000051 : Rat) / 200000000000000000000), R := ((260484351875000000051 : Rat) / 100000000000000000000), D0 := ((260484351875000000051 : Rat) / 100000000000000000000), D1 := ((78736841875000000051 : Rat) / 100000000000000000000), D2 := ((4690851875000000051 : Rat) / 100000000000000000000), D3 := ((14072555625000000153 : Rat) / 200000000000000000000), D4 := ((38196173839285694341 : Rat) / 200000000000000000000), LB := ((2126747511477789 : Rat) / 50000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((260484351875000000051 : Rat) / 100000000000000000000), R := ((132587601875000000051 : Rat) / 50000000000000000000), D0 := ((132587601875000000051 : Rat) / 50000000000000000000), D1 := ((41713846875000000051 : Rat) / 50000000000000000000), D2 := ((4690851875000000051 : Rat) / 50000000000000000000), D3 := ((4690851875000000051 : Rat) / 100000000000000000000), D4 := ((3350532196428569429 : Rat) / 20000000000000000000), LB := ((27505506410203717 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((132587601875000000051 : Rat) / 50000000000000000000), R := ((53937674839285714329 : Rat) / 20000000000000000000), D0 := ((53937674839285714329 : Rat) / 20000000000000000000), D1 := ((17588172839285714329 : Rat) / 20000000000000000000), D2 := ((2778974839285714329 : Rat) / 20000000000000000000), D3 := ((4513170446428571543 : Rat) / 100000000000000000000), D4 := ((6030904553571423547 : Rat) / 50000000000000000000), LB := ((7305488649040903 : Rat) / 10000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((53937674839285714329 : Rat) / 20000000000000000000), R := ((1083266667232142858123 : Rat) / 400000000000000000000), D0 := ((1083266667232142858123 : Rat) / 400000000000000000000), D1 := ((356276627232142858123 : Rat) / 400000000000000000000), D2 := ((60092667232142858123 : Rat) / 400000000000000000000), D3 := ((4513170446428571543 : Rat) / 80000000000000000000), D4 := ((7548638660714275551 : Rat) / 100000000000000000000), LB := ((6259236678677643 : Rat) / 500000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1083266667232142858123 : Rat) / 400000000000000000000), R := ((2171046504910714287789 : Rat) / 800000000000000000000), D0 := ((2171046504910714287789 : Rat) / 800000000000000000000), D1 := ((717066424910714287789 : Rat) / 800000000000000000000), D2 := ((124698504910714287789 : Rat) / 800000000000000000000), D3 := ((49644874910714286973 : Rat) / 800000000000000000000), D4 := ((25681384196428530661 : Rat) / 400000000000000000000), LB := ((68581815172249 : Rat) / 6250000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2171046504910714287789 : Rat) / 800000000000000000000), R := ((543889918839285714833 : Rat) / 200000000000000000000), D0 := ((543889918839285714833 : Rat) / 200000000000000000000), D1 := ((180394898839285714833 : Rat) / 200000000000000000000), D2 := ((32302918839285714833 : Rat) / 200000000000000000000), D3 := ((13539511339285714629 : Rat) / 200000000000000000000), D4 := ((46849597946428489779 : Rat) / 800000000000000000000), LB := ((5043234327942181 : Rat) / 5000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((543889918839285714833 : Rat) / 200000000000000000000), R := ((4355632521160714290207 : Rat) / 1600000000000000000000), D0 := ((4355632521160714290207 : Rat) / 1600000000000000000000), D1 := ((1447672361160714290207 : Rat) / 1600000000000000000000), D2 := ((262936521160714290207 : Rat) / 1600000000000000000000), D3 := ((4513170446428571543 : Rat) / 64000000000000000000), D4 := ((10584106874999979559 : Rat) / 200000000000000000000), LB := ((8558847491129451 : Rat) / 2000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4355632521160714290207 : Rat) / 1600000000000000000000), R := ((17440582766428571447 : Rat) / 6400000000000000000), D0 := ((17440582766428571447 : Rat) / 6400000000000000000), D1 := ((5808742126428571447 : Rat) / 6400000000000000000), D2 := ((1069798766428571447 : Rat) / 6400000000000000000), D3 := ((58671215803571430059 : Rat) / 800000000000000000000), D4 := ((80159684553571264929 : Rat) / 1600000000000000000000), LB := ((3197471241478539 : Rat) / 2500000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((17440582766428571447 : Rat) / 6400000000000000000), R := ((8724804553660714295043 : Rat) / 3200000000000000000000), D0 := ((8724804553660714295043 : Rat) / 3200000000000000000000), D1 := ((2908884233660714295043 : Rat) / 3200000000000000000000), D2 := ((539412553660714295043 : Rat) / 3200000000000000000000), D3 := ((239198033660714291779 : Rat) / 3200000000000000000000), D4 := ((37823257053571346693 : Rat) / 800000000000000000000), LB := ((1045148575795407 : Rat) / 250000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8724804553660714295043 : Rat) / 3200000000000000000000), R := ((4364658862053571433293 : Rat) / 1600000000000000000000), D0 := ((4364658862053571433293 : Rat) / 1600000000000000000000), D1 := ((1456698702053571433293 : Rat) / 1600000000000000000000), D2 := ((271962862053571433293 : Rat) / 1600000000000000000000), D3 := ((121855602053571431661 : Rat) / 1600000000000000000000), D4 := ((146779857767856815229 : Rat) / 3200000000000000000000), LB := ((649861378464367 : Rat) / 200000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4364658862053571433293 : Rat) / 1600000000000000000000), R := ((8733830894553571438129 : Rat) / 3200000000000000000000), D0 := ((8733830894553571438129 : Rat) / 3200000000000000000000), D1 := ((2917910574553571438129 : Rat) / 3200000000000000000000), D2 := ((548438894553571438129 : Rat) / 3200000000000000000000), D3 := ((49644874910714286973 : Rat) / 640000000000000000000), D4 := ((71133343660714121843 : Rat) / 1600000000000000000000), LB := ((2511585341837319 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8733830894553571438129 : Rat) / 3200000000000000000000), R := ((1092293008125000001209 : Rat) / 400000000000000000000), D0 := ((1092293008125000001209 : Rat) / 400000000000000000000), D1 := ((365302968125000001209 : Rat) / 400000000000000000000), D2 := ((69119008125000001209 : Rat) / 400000000000000000000), D3 := ((31592193125000000801 : Rat) / 400000000000000000000), D4 := ((137753516874999672143 : Rat) / 3200000000000000000000), LB := ((19739805090754903 : Rat) / 10000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1092293008125000001209 : Rat) / 400000000000000000000), R := ((1748571447089285716243 : Rat) / 640000000000000000000), D0 := ((1748571447089285716243 : Rat) / 640000000000000000000), D1 := ((585387383089285716243 : Rat) / 640000000000000000000), D2 := ((111493047089285716243 : Rat) / 640000000000000000000), D3 := ((257250715446428577951 : Rat) / 3200000000000000000000), D4 := ((666201732142855503 : Rat) / 16000000000000000000), LB := ((16440081795451311 : Rat) / 10000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1748571447089285716243 : Rat) / 640000000000000000000), R := ((4373685202946428576379 : Rat) / 1600000000000000000000), D0 := ((4373685202946428576379 : Rat) / 1600000000000000000000), D1 := ((1465725042946428576379 : Rat) / 1600000000000000000000), D2 := ((280989202946428576379 : Rat) / 1600000000000000000000), D3 := ((130881942946428574747 : Rat) / 1600000000000000000000), D4 := ((128727175982142529057 : Rat) / 3200000000000000000000), LB := ((15302600933786437 : Rat) / 10000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4373685202946428576379 : Rat) / 1600000000000000000000), R := ((8751883576339285724301 : Rat) / 3200000000000000000000), D0 := ((8751883576339285724301 : Rat) / 3200000000000000000000), D1 := ((2935963256339285724301 : Rat) / 3200000000000000000000), D2 := ((566491576339285724301 : Rat) / 3200000000000000000000), D3 := ((266277056339285721037 : Rat) / 3200000000000000000000), D4 := ((62107002767856978757 : Rat) / 1600000000000000000000), LB := ((3285073466331001 : Rat) / 2000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8751883576339285724301 : Rat) / 3200000000000000000000), R := ((2189099186696428573961 : Rat) / 800000000000000000000), D0 := ((2189099186696428573961 : Rat) / 800000000000000000000), D1 := ((735119106696428573961 : Rat) / 800000000000000000000), D2 := ((142751186696428573961 : Rat) / 800000000000000000000), D3 := ((13539511339285714629 : Rat) / 160000000000000000000), D4 := ((119700835089285385971 : Rat) / 3200000000000000000000), LB := ((19920065061223013 : Rat) / 10000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2189099186696428573961 : Rat) / 800000000000000000000), R := ((8760909917232142867387 : Rat) / 3200000000000000000000), D0 := ((8760909917232142867387 : Rat) / 3200000000000000000000), D1 := ((2944989597232142867387 : Rat) / 3200000000000000000000), D2 := ((575517917232142867387 : Rat) / 3200000000000000000000), D3 := ((275303397232142864123 : Rat) / 3200000000000000000000), D4 := ((28796916160714203607 : Rat) / 800000000000000000000), LB := ((2591397225060077 : Rat) / 1000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8760909917232142867387 : Rat) / 3200000000000000000000), R := ((876542308767857143893 : Rat) / 320000000000000000000), D0 := ((876542308767857143893 : Rat) / 320000000000000000000), D1 := ((294950276767857143893 : Rat) / 320000000000000000000), D2 := ((58003108767857143893 : Rat) / 320000000000000000000), D3 := ((139908283839285717833 : Rat) / 1600000000000000000000), D4 := ((22134898839285648577 : Rat) / 640000000000000000000), LB := ((17276137339597153 : Rat) / 5000000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((876542308767857143893 : Rat) / 320000000000000000000), R := ((8769936258125000010473 : Rat) / 3200000000000000000000), D0 := ((8769936258125000010473 : Rat) / 3200000000000000000000), D1 := ((2954015938125000010473 : Rat) / 3200000000000000000000), D2 := ((584544258125000010473 : Rat) / 3200000000000000000000), D3 := ((284329738125000007209 : Rat) / 3200000000000000000000), D4 := ((53080661874999835671 : Rat) / 1600000000000000000000), LB := ((2300043813156849 : Rat) / 500000000000000000) },
  { w1 := ((8391843467619307 : Rat) / 10000000000000000), w2 := ((23076484475740223 : Rat) / 500000000000000000), w3 := ((1000732136480147 : Rat) / 6250000000000000), w4 := ((140808450078083 : Rat) / 1000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132587601875000000051 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8769936258125000010473 : Rat) / 3200000000000000000000), R := ((68550386160714285797 : Rat) / 25000000000000000000), D0 := ((68550386160714285797 : Rat) / 25000000000000000000), D1 := ((23113508660714285797 : Rat) / 25000000000000000000), D2 := ((4602011160714285797 : Rat) / 25000000000000000000), D3 := ((4513170446428571543 : Rat) / 50000000000000000000), D4 := ((101648153303571099799 : Rat) / 3200000000000000000000), LB := ((6044983457496489 : Rat) / 1000000000000000000) }
]

def block386RightChunk000L : Rat := ((87090997767857143023 : Rat) / 50000000000000000000)
def block386RightChunk000R : Rat := ((68550386160714285797 : Rat) / 25000000000000000000)

def block386RightChunk000Certificate : Bool :=
  allBoxesValid block386RightChunk000 &&
  coversFromBool block386RightChunk000 block386RightChunk000L block386RightChunk000R

theorem block386RightChunk000Certificate_eq_true :
    block386RightChunk000Certificate = true := by
  native_decide

def block386RightChainCertificate : Bool :=
  decide (
    block386RightL = ((87090997767857143023 : Rat) / 50000000000000000000) /\
    ((68550386160714285797 : Rat) / 25000000000000000000) = block386RightR)

theorem block386RightChainCertificate_eq_true :
    block386RightChainCertificate = true := by
  native_decide

def block386LeftBoxCount : Nat := boxCount block386LeftBoxes
def block386RightBoxCount : Nat := 59

def block386_rational_certificate : Prop :=
    block386LeftCertificate = true /\
    block386RightChainCertificate = true /\
    block386RightChunk000Certificate = true

theorem block386_rational_certificate_proof :
    block386_rational_certificate := by
  exact ⟨block386LeftCertificate_eq_true, block386RightChainCertificate_eq_true, block386RightChunk000Certificate_eq_true⟩

end Block386
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block386

open Set

def block386W1 : Rat := ((8391843467619307 : Rat) / 10000000000000000)
def block386W2 : Rat := ((23076484475740223 : Rat) / 500000000000000000)
def block386W3 : Rat := ((1000732136480147 : Rat) / 6250000000000000)
def block386W4 : Rat := ((140808450078083 : Rat) / 1000000000000000)
def block386S1 : Rat := ((18174751 : Rat) / 10000000)
def block386S2 : Rat := ((511587 : Rat) / 200000)
def block386S3 : Rat := ((132587601875000000051 : Rat) / 50000000000000000000)
def block386S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block386V (y : ℝ) : ℝ :=
  ratPotential block386W1 block386W2 block386W3 block386W4 block386S1 block386S2 block386S3 block386S4 y

def block386LeftParamsCertificate : Bool :=
  allBoxesSameParams block386LeftBoxes block386W1 block386W2 block386W3 block386W4 block386S1 block386S2 block386S3 block386S4

theorem block386LeftParamsCertificate_eq_true :
    block386LeftParamsCertificate = true := by
  native_decide

theorem block386_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block386LeftL : ℝ) (block386LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block386S1 : ℝ))
    (hy2ne : y ≠ (block386S2 : ℝ))
    (hy3ne : y ≠ (block386S3 : ℝ))
    (hy4ne : y ≠ (block386S4 : ℝ)) :
    0 < block386V y := by
  have hcert := block386LeftCertificate_eq_true
  unfold block386LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block386LeftBoxes) (lo := block386LeftL) (hi := block386LeftR)
    (w1 := block386W1) (w2 := block386W2) (w3 := block386W3) (w4 := block386W4)
    (s1 := block386S1) (s2 := block386S2) (s3 := block386S3) (s4 := block386S4)
    hboxes hcover block386LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block386RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block386RightChunk000 block386W1 block386W2 block386W3 block386W4 block386S1 block386S2 block386S3 block386S4

theorem block386RightChunk000ParamsCertificate_eq_true :
    block386RightChunk000ParamsCertificate = true := by
  native_decide

theorem block386_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block386RightChunk000L : ℝ) (block386RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block386S1 : ℝ))
    (hy2ne : y ≠ (block386S2 : ℝ))
    (hy3ne : y ≠ (block386S3 : ℝ))
    (hy4ne : y ≠ (block386S4 : ℝ)) :
    0 < block386V y := by
  have hcert := block386RightChunk000Certificate_eq_true
  unfold block386RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block386RightChunk000) (lo := block386RightChunk000L) (hi := block386RightChunk000R)
    (w1 := block386W1) (w2 := block386W2) (w3 := block386W3) (w4 := block386W4)
    (s1 := block386S1) (s2 := block386S2) (s3 := block386S3) (s4 := block386S4)
    hboxes hcover block386RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block386_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block386RightL : ℝ) (block386RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block386S1 : ℝ))
    (hy2ne : y ≠ (block386S2 : ℝ))
    (hy3ne : y ≠ (block386S3 : ℝ))
    (hy4ne : y ≠ (block386S4 : ℝ)) :
    0 < block386V y := by
  have hL : (block386RightChunk000L : ℝ) = (block386RightL : ℝ) := by
    norm_num [block386RightChunk000L, block386RightL]
  have hR : (block386RightChunk000R : ℝ) = (block386RightR : ℝ) := by
    norm_num [block386RightChunk000R, block386RightR]
  have hyc : y ∈ Icc (block386RightChunk000L : ℝ) (block386RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block386_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block386_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block386LeftL : ℝ) (block386LeftR : ℝ) →
    y ≠ 0 → y ≠ (block386S1 : ℝ) → y ≠ (block386S2 : ℝ) →
    y ≠ (block386S3 : ℝ) → y ≠ (block386S4 : ℝ) → 0 < block386V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block386RightL : ℝ) (block386RightR : ℝ) →
    y ≠ 0 → y ≠ (block386S1 : ℝ) → y ≠ (block386S2 : ℝ) →
    y ≠ (block386S3 : ℝ) → y ≠ (block386S4 : ℝ) → 0 < block386V y)

theorem block386_reallog_certificate_proof :
    block386_reallog_certificate := by
  exact ⟨block386_left_V_pos, block386_right_V_pos⟩

end Block386
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block386.block386V
#check Erdos1038Lean.M1817475.Block386.block386_left_V_pos
#check Erdos1038Lean.M1817475.Block386.block386_right_V_pos
#check Erdos1038Lean.M1817475.Block386.block386_reallog_certificate_proof
