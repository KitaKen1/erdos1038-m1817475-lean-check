/-
Self-contained Lean4Web paste file.
Block 269 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block269

def block269LeftL : Rat := ((3823462053571428583 : Rat) / 5000000000000000000)
def block269LeftR : Rat := ((38244395089285714401 : Rat) / 50000000000000000000)
def block269RightL : Rat := ((8823462053571428583 : Rat) / 5000000000000000000)
def block269RightR : Rat := ((138244395089285714401 : Rat) / 50000000000000000000)

def block269LeftBoxes : List RatBox := [
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3823462053571428583 : Rat) / 5000000000000000000), R := ((38244395089285714401 : Rat) / 50000000000000000000), D0 := ((38244395089285714401 : Rat) / 50000000000000000000), D1 := ((5263913446428571417 : Rat) / 5000000000000000000), D2 := ((8966212946428571417 : Rat) / 5000000000000000000), D3 := ((19562634660714285671 : Rat) / 10000000000000000000), D4 := ((25398982633928570143 : Rat) / 12500000000000000000), LB := ((809584694268211 : Rat) / 625000000000000000) }
]

def block269LeftCertificate : Bool :=
  allBoxesValid block269LeftBoxes &&
  coversFromBool block269LeftBoxes block269LeftL block269LeftR

theorem block269LeftCertificate_eq_true :
    block269LeftCertificate = true := by
  native_decide

def block269RightChunk000 : List RatBox := [
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((8823462053571428583 : Rat) / 5000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((263913446428571417 : Rat) / 5000000000000000000), D2 := ((3966212946428571417 : Rat) / 5000000000000000000), D3 := ((9562634660714285671 : Rat) / 10000000000000000000), D4 := ((12898982633928570143 : Rat) / 12500000000000000000), LB := ((153008728003447 : Rat) / 62500000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((24478398035714283201 : Rat) / 25000000000000000000), LB := ((1388307307099547 : Rat) / 5000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((15222649285714283201 : Rat) / 25000000000000000000), LB := ((3628404643549501 : Rat) / 20000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((4406933392857142837 : Rat) / 10000000000000000000), D4 := ((12908712098214283201 : Rat) / 25000000000000000000), LB := ((916479915578261 : Rat) / 50000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((10594774910714283201 : Rat) / 25000000000000000000), LB := ((1900106222083473 : Rat) / 40000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((3249964799107142837 : Rat) / 10000000000000000000), D4 := ((10016290613839283201 : Rat) / 25000000000000000000), LB := ((269713225180173 : Rat) / 12500000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((3018571080357142837 : Rat) / 10000000000000000000), D4 := ((9437806316964283201 : Rat) / 25000000000000000000), LB := ((11662921359061551 : Rat) / 500000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2902874220982142837 : Rat) / 10000000000000000000), D4 := ((9148564168526783201 : Rat) / 25000000000000000000), LB := ((832733777112557 : Rat) / 62500000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2787177361607142837 : Rat) / 10000000000000000000), D4 := ((8859322020089283201 : Rat) / 25000000000000000000), LB := ((880375895282337 : Rat) / 200000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2671480502232142837 : Rat) / 10000000000000000000), D4 := ((8570079871651783201 : Rat) / 25000000000000000000), LB := ((2052969961377077 : Rat) / 250000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2613632072544642837 : Rat) / 10000000000000000000), D4 := ((8425458797433033201 : Rat) / 25000000000000000000), LB := ((1176562038254017 : Rat) / 250000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((8280837723214283201 : Rat) / 25000000000000000000), LB := ((1531483244532561 : Rat) / 1000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((2497935213169642837 : Rat) / 10000000000000000000), D4 := ((8136216648995533201 : Rat) / 25000000000000000000), LB := ((4395454695036161 : Rat) / 1000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((2469010998325892837 : Rat) / 10000000000000000000), D4 := ((8063906111886158201 : Rat) / 25000000000000000000), LB := ((77465146897919 : Rat) / 25000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((2440086783482142837 : Rat) / 10000000000000000000), D4 := ((7991595574776783201 : Rat) / 25000000000000000000), LB := ((4743380105422107 : Rat) / 2500000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((2411162568638392837 : Rat) / 10000000000000000000), D4 := ((7919285037667408201 : Rat) / 25000000000000000000), LB := ((7949623995694433 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((12718992651 : Rat) / 5120000000), D0 := ((12718992651 : Rat) / 5120000000), D1 := ((3413520139 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((2382238353794642837 : Rat) / 10000000000000000000), D4 := ((7846974500558033201 : Rat) / 25000000000000000000), LB := ((521184569171429 : Rat) / 200000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12718992651 : Rat) / 5120000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((377634549 : Rat) / 5120000000), D3 := ((2367776246372767837 : Rat) / 10000000000000000000), D4 := ((7810819232003345701 : Rat) / 25000000000000000000), LB := ((10702173890327349 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((12733801849 : Rat) / 5120000000), D0 := ((12733801849 : Rat) / 5120000000), D1 := ((3428329337 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((2353314138950892837 : Rat) / 10000000000000000000), D4 := ((7774663963448658201 : Rat) / 25000000000000000000), LB := ((4255235082680081 : Rat) / 2500000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12733801849 : Rat) / 5120000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((362825351 : Rat) / 5120000000), D3 := ((2338852031529017837 : Rat) / 10000000000000000000), D4 := ((7738508694893970701 : Rat) / 25000000000000000000), LB := ((12914603430822513 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((12748611047 : Rat) / 5120000000), D0 := ((12748611047 : Rat) / 5120000000), D1 := ((688627707 : Rat) / 1024000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((2324389924107142837 : Rat) / 10000000000000000000), D4 := ((7702353426339283201 : Rat) / 25000000000000000000), LB := ((9091236706926797 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12748611047 : Rat) / 5120000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((348016153 : Rat) / 5120000000), D3 := ((2309927816685267837 : Rat) / 10000000000000000000), D4 := ((7666198157784595701 : Rat) / 25000000000000000000), LB := ((694633241989373 : Rat) / 1250000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((2552684049 : Rat) / 1024000000), D0 := ((2552684049 : Rat) / 1024000000), D1 := ((3457947733 : Rat) / 5120000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((2295465709263392837 : Rat) / 10000000000000000000), D4 := ((7630042889229908201 : Rat) / 25000000000000000000), LB := ((2318669410820151 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((2552684049 : Rat) / 1024000000), R := ((25534245089 : Rat) / 10240000000), D0 := ((25534245089 : Rat) / 10240000000), D1 := ((1384660013 : Rat) / 2048000000), D2 := ((66641391 : Rat) / 1024000000), D3 := ((2281003601841517837 : Rat) / 10000000000000000000), D4 := ((7593887620675220701 : Rat) / 25000000000000000000), LB := ((13278037898863393 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25534245089 : Rat) / 10240000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((659009311 : Rat) / 10240000000), D3 := ((2273772548130580337 : Rat) / 10000000000000000000), D4 := ((7575809986397876951 : Rat) / 25000000000000000000), LB := ((74458986477767 : Rat) / 62500000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((25549054287 : Rat) / 10240000000), D0 := ((25549054287 : Rat) / 10240000000), D1 := ((6938109263 : Rat) / 10240000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((2266541494419642837 : Rat) / 10000000000000000000), D4 := ((7557732352120533201 : Rat) / 25000000000000000000), LB := ((10627346478560007 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25549054287 : Rat) / 10240000000), R := ((12778229443 : Rat) / 5120000000), D0 := ((12778229443 : Rat) / 5120000000), D1 := ((3472756931 : Rat) / 5120000000), D2 := ((644200113 : Rat) / 10240000000), D3 := ((2259310440708705337 : Rat) / 10000000000000000000), D4 := ((7539654717843189451 : Rat) / 25000000000000000000), LB := ((4710378079260391 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12778229443 : Rat) / 5120000000), R := ((5112772697 : Rat) / 2048000000), D0 := ((5112772697 : Rat) / 2048000000), D1 := ((6952918461 : Rat) / 10240000000), D2 := ((318397757 : Rat) / 5120000000), D3 := ((2252079386997767837 : Rat) / 10000000000000000000), D4 := ((7521577083565845701 : Rat) / 25000000000000000000), LB := ((829468983542303 : Rat) / 1000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((5112772697 : Rat) / 2048000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((125878183 : Rat) / 2048000000), D3 := ((2244848333286830337 : Rat) / 10000000000000000000), D4 := ((7503499449288501951 : Rat) / 25000000000000000000), LB := ((7250202460999389 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((25578672683 : Rat) / 10240000000), D0 := ((25578672683 : Rat) / 10240000000), D1 := ((6967727659 : Rat) / 10240000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((2237617279575892837 : Rat) / 10000000000000000000), D4 := ((7485421815011158201 : Rat) / 25000000000000000000), LB := ((1572095606578311 : Rat) / 2500000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25578672683 : Rat) / 10240000000), R := ((12793038641 : Rat) / 5120000000), D0 := ((12793038641 : Rat) / 5120000000), D1 := ((3487566129 : Rat) / 5120000000), D2 := ((614581717 : Rat) / 10240000000), D3 := ((2230386225864955337 : Rat) / 10000000000000000000), D4 := ((7467344180733814451 : Rat) / 25000000000000000000), LB := ((5410353094131293 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12793038641 : Rat) / 5120000000), R := ((25593481881 : Rat) / 10240000000), D0 := ((25593481881 : Rat) / 10240000000), D1 := ((6982536857 : Rat) / 10240000000), D2 := ((303588559 : Rat) / 5120000000), D3 := ((2223155172154017837 : Rat) / 10000000000000000000), D4 := ((7449266546456470701 : Rat) / 25000000000000000000), LB := ((4617274423091011 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25593481881 : Rat) / 10240000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((599772519 : Rat) / 10240000000), D3 := ((2215924118443080337 : Rat) / 10000000000000000000), D4 := ((7431188912179126951 : Rat) / 25000000000000000000), LB := ((3910344690397083 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((25608291079 : Rat) / 10240000000), D0 := ((25608291079 : Rat) / 10240000000), D1 := ((1399469211 : Rat) / 2048000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((2208693064732142837 : Rat) / 10000000000000000000), D4 := ((7413111277901783201 : Rat) / 25000000000000000000), LB := ((6581604640960581 : Rat) / 20000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25608291079 : Rat) / 10240000000), R := ((12807847839 : Rat) / 5120000000), D0 := ((12807847839 : Rat) / 5120000000), D1 := ((3502375327 : Rat) / 5120000000), D2 := ((584963321 : Rat) / 10240000000), D3 := ((2201462011021205337 : Rat) / 10000000000000000000), D4 := ((7395033643624439451 : Rat) / 25000000000000000000), LB := ((344990978427967 : Rat) / 1250000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12807847839 : Rat) / 5120000000), R := ((25623100277 : Rat) / 10240000000), D0 := ((25623100277 : Rat) / 10240000000), D1 := ((7012155253 : Rat) / 10240000000), D2 := ((288779361 : Rat) / 5120000000), D3 := ((2194230957310267837 : Rat) / 10000000000000000000), D4 := ((7376956009347095701 : Rat) / 25000000000000000000), LB := ((11595229399952167 : Rat) / 50000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25623100277 : Rat) / 10240000000), R := ((6407626219 : Rat) / 2560000000), D0 := ((6407626219 : Rat) / 2560000000), D1 := ((1754889963 : Rat) / 2560000000), D2 := ((570154123 : Rat) / 10240000000), D3 := ((2186999903599330337 : Rat) / 10000000000000000000), D4 := ((7358878375069751951 : Rat) / 25000000000000000000), LB := ((3939054997214031 : Rat) / 20000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6407626219 : Rat) / 2560000000), R := ((1025516379 : Rat) / 409600000), D0 := ((1025516379 : Rat) / 409600000), D1 := ((7026964451 : Rat) / 10240000000), D2 := ((140687381 : Rat) / 2560000000), D3 := ((2179768849888392837 : Rat) / 10000000000000000000), D4 := ((7340800740792408201 : Rat) / 25000000000000000000), LB := ((1712792394713003 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1025516379 : Rat) / 409600000), R := ((12822657037 : Rat) / 5120000000), D0 := ((12822657037 : Rat) / 5120000000), D1 := ((140687381 : Rat) / 204800000), D2 := ((22213797 : Rat) / 409600000), D3 := ((2172537796177455337 : Rat) / 10000000000000000000), D4 := ((7322723106515064451 : Rat) / 25000000000000000000), LB := ((620124585467563 : Rat) / 4000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12822657037 : Rat) / 5120000000), R := ((25652718673 : Rat) / 10240000000), D0 := ((25652718673 : Rat) / 10240000000), D1 := ((7041773649 : Rat) / 10240000000), D2 := ((273970163 : Rat) / 5120000000), D3 := ((2165306742466517837 : Rat) / 10000000000000000000), D4 := ((7304645472237720701 : Rat) / 25000000000000000000), LB := ((148360944366821 : Rat) / 1000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25652718673 : Rat) / 10240000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((540535727 : Rat) / 10240000000), D3 := ((2158075688755580337 : Rat) / 10000000000000000000), D4 := ((7286567837960376951 : Rat) / 25000000000000000000), LB := ((757133877044569 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((25667527871 : Rat) / 10240000000), D0 := ((25667527871 : Rat) / 10240000000), D1 := ((7056582847 : Rat) / 10240000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((2150844635044642837 : Rat) / 10000000000000000000), D4 := ((7268490203683033201 : Rat) / 25000000000000000000), LB := ((16439275281676657 : Rat) / 100000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25667527871 : Rat) / 10240000000), R := ((2567493247 : Rat) / 1024000000), D0 := ((2567493247 : Rat) / 1024000000), D1 := ((3531993723 : Rat) / 5120000000), D2 := ((525726529 : Rat) / 10240000000), D3 := ((2143613581333705337 : Rat) / 10000000000000000000), D4 := ((7250412569405689451 : Rat) / 25000000000000000000), LB := ((4685732140637111 : Rat) / 25000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((2567493247 : Rat) / 1024000000), R := ((25682337069 : Rat) / 10240000000), D0 := ((25682337069 : Rat) / 10240000000), D1 := ((1414278409 : Rat) / 2048000000), D2 := ((51832193 : Rat) / 1024000000), D3 := ((2136382527622767837 : Rat) / 10000000000000000000), D4 := ((7232334935128345701 : Rat) / 25000000000000000000), LB := ((22071342575019637 : Rat) / 100000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25682337069 : Rat) / 10240000000), R := ((6422435417 : Rat) / 2560000000), D0 := ((6422435417 : Rat) / 2560000000), D1 := ((1769699161 : Rat) / 2560000000), D2 := ((510917331 : Rat) / 10240000000), D3 := ((2129151473911830337 : Rat) / 10000000000000000000), D4 := ((7214257300851001951 : Rat) / 25000000000000000000), LB := ((13221461998841333 : Rat) / 50000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6422435417 : Rat) / 2560000000), R := ((25697146267 : Rat) / 10240000000), D0 := ((25697146267 : Rat) / 10240000000), D1 := ((7086201243 : Rat) / 10240000000), D2 := ((125878183 : Rat) / 2560000000), D3 := ((2121920420200892837 : Rat) / 10000000000000000000), D4 := ((7196179666573658201 : Rat) / 25000000000000000000), LB := ((39846026116723 : Rat) / 125000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25697146267 : Rat) / 10240000000), R := ((12852275433 : Rat) / 5120000000), D0 := ((12852275433 : Rat) / 5120000000), D1 := ((3546802921 : Rat) / 5120000000), D2 := ((496108133 : Rat) / 10240000000), D3 := ((2114689366489955337 : Rat) / 10000000000000000000), D4 := ((7178102032296314451 : Rat) / 25000000000000000000), LB := ((38392965545008817 : Rat) / 100000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12852275433 : Rat) / 5120000000), R := ((5142391093 : Rat) / 2048000000), D0 := ((5142391093 : Rat) / 2048000000), D1 := ((7101010441 : Rat) / 10240000000), D2 := ((244351767 : Rat) / 5120000000), D3 := ((2107458312779017837 : Rat) / 10000000000000000000), D4 := ((7160024398018970701 : Rat) / 25000000000000000000), LB := ((1150303012348447 : Rat) / 2500000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((5142391093 : Rat) / 2048000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((96259787 : Rat) / 2048000000), D3 := ((2100227259068080337 : Rat) / 10000000000000000000), D4 := ((7141946763741626951 : Rat) / 25000000000000000000), LB := ((547559280752119 : Rat) / 1000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((25726764663 : Rat) / 10240000000), D0 := ((25726764663 : Rat) / 10240000000), D1 := ((7115819639 : Rat) / 10240000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((7123869129464283201 : Rat) / 25000000000000000000), LB := ((6464696377239121 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25726764663 : Rat) / 10240000000), R := ((12867084631 : Rat) / 5120000000), D0 := ((12867084631 : Rat) / 5120000000), D1 := ((3561612119 : Rat) / 5120000000), D2 := ((466489737 : Rat) / 10240000000), D3 := ((2085765151646205337 : Rat) / 10000000000000000000), D4 := ((7105791495186939451 : Rat) / 25000000000000000000), LB := ((3785439687767067 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12867084631 : Rat) / 5120000000), R := ((25741573861 : Rat) / 10240000000), D0 := ((25741573861 : Rat) / 10240000000), D1 := ((7130628837 : Rat) / 10240000000), D2 := ((229542569 : Rat) / 5120000000), D3 := ((2078534097935267837 : Rat) / 10000000000000000000), D4 := ((7087713860909595701 : Rat) / 25000000000000000000), LB := ((8796603699939287 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25741573861 : Rat) / 10240000000), R := ((1287448923 : Rat) / 512000000), D0 := ((1287448923 : Rat) / 512000000), D1 := ((1784508359 : Rat) / 2560000000), D2 := ((451680539 : Rat) / 10240000000), D3 := ((2071303044224330337 : Rat) / 10000000000000000000), D4 := ((7069636226632251951 : Rat) / 25000000000000000000), LB := ((5072221621758577 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1287448923 : Rat) / 512000000), R := ((25756383059 : Rat) / 10240000000), D0 := ((25756383059 : Rat) / 10240000000), D1 := ((1429087607 : Rat) / 2048000000), D2 := ((22213797 : Rat) / 512000000), D3 := ((2064071990513392837 : Rat) / 10000000000000000000), D4 := ((7051558592354908201 : Rat) / 25000000000000000000), LB := ((5808545581226787 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25756383059 : Rat) / 10240000000), R := ((12881893829 : Rat) / 5120000000), D0 := ((12881893829 : Rat) / 5120000000), D1 := ((3576421317 : Rat) / 5120000000), D2 := ((436871341 : Rat) / 10240000000), D3 := ((2056840936802455337 : Rat) / 10000000000000000000), D4 := ((7033480958077564451 : Rat) / 25000000000000000000), LB := ((2643473550454467 : Rat) / 2000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12881893829 : Rat) / 5120000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((214733371 : Rat) / 5120000000), D3 := ((2049609883091517837 : Rat) / 10000000000000000000), D4 := ((7015403323800220701 : Rat) / 25000000000000000000), LB := ((577412372879893 : Rat) / 4000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((12896703027 : Rat) / 5120000000), D0 := ((12896703027 : Rat) / 5120000000), D1 := ((718246103 : Rat) / 1024000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((2035147775669642837 : Rat) / 10000000000000000000), D4 := ((6979248055245533201 : Rat) / 25000000000000000000), LB := ((213325947260401 : Rat) / 400000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12896703027 : Rat) / 5120000000), R := ((6452053813 : Rat) / 2560000000), D0 := ((6452053813 : Rat) / 2560000000), D1 := ((1799317557 : Rat) / 2560000000), D2 := ((199924173 : Rat) / 5120000000), D3 := ((2020685668247767837 : Rat) / 10000000000000000000), D4 := ((6943092786690845701 : Rat) / 25000000000000000000), LB := ((4892153734771809 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6452053813 : Rat) / 2560000000), R := ((516460489 : Rat) / 204800000), D0 := ((516460489 : Rat) / 204800000), D1 := ((3606039713 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 2560000000), D3 := ((2006223560825892837 : Rat) / 10000000000000000000), D4 := ((6906937518136158201 : Rat) / 25000000000000000000), LB := ((741330123575773 : Rat) / 500000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((516460489 : Rat) / 204800000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 204800000), D3 := ((1991761453404017837 : Rat) / 10000000000000000000), D4 := ((6870782249581470701 : Rat) / 25000000000000000000), LB := ((4098586106792701 : Rat) / 2000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((6466863011 : Rat) / 2560000000), D0 := ((6466863011 : Rat) / 2560000000), D1 := ((362825351 : Rat) / 512000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1977299345982142837 : Rat) / 10000000000000000000), D4 := ((6834626981026783201 : Rat) / 25000000000000000000), LB := ((317279628487821 : Rat) / 40000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6466863011 : Rat) / 2560000000), R := ((647426761 : Rat) / 256000000), D0 := ((647426761 : Rat) / 256000000), D1 := ((910765677 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 2560000000), D3 := ((1948375131138392837 : Rat) / 10000000000000000000), D4 := ((6762316443917408201 : Rat) / 25000000000000000000), LB := ((7488990323532563 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((647426761 : Rat) / 256000000), R := ((6481672209 : Rat) / 2560000000), D0 := ((6481672209 : Rat) / 2560000000), D1 := ((1828935953 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 256000000), D3 := ((1919450916294642837 : Rat) / 10000000000000000000), D4 := ((6690005906808033201 : Rat) / 25000000000000000000), LB := ((3308813663287169 : Rat) / 1000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6481672209 : Rat) / 2560000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((66641391 : Rat) / 2560000000), D3 := ((1890526701450892837 : Rat) / 10000000000000000000), D4 := ((6617695369698658201 : Rat) / 25000000000000000000), LB := ((10986120925489229 : Rat) / 2000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((3251943003 : Rat) / 1280000000), D0 := ((3251943003 : Rat) / 1280000000), D1 := ((7404599 : Rat) / 10240000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((6545384832589283201 : Rat) / 25000000000000000000), LB := ((2858585896103827 : Rat) / 1000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3251943003 : Rat) / 1280000000), R := ((1629673801 : Rat) / 640000000), D0 := ((1629673801 : Rat) / 640000000), D1 := ((466489737 : Rat) / 640000000), D2 := ((22213797 : Rat) / 1280000000), D3 := ((1803754056919642837 : Rat) / 10000000000000000000), D4 := ((6400763758370533201 : Rat) / 25000000000000000000), LB := ((247816626690929 : Rat) / 25000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1629673801 : Rat) / 640000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 640000000), D3 := ((1745905627232142837 : Rat) / 10000000000000000000), D4 := ((6256142684151783201 : Rat) / 25000000000000000000), LB := ((1297898839837941 : Rat) / 125000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((410899808767857142837 : Rat) / 160000000000000000000), D0 := ((410899808767857142837 : Rat) / 160000000000000000000), D1 := ((120103792767857142837 : Rat) / 160000000000000000000), D2 := ((1630208767857142837 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((5966900535714283201 : Rat) / 25000000000000000000), LB := ((8063570484377891 : Rat) / 500000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((410899808767857142837 : Rat) / 160000000000000000000), R := ((823429826303571428511 : Rat) / 320000000000000000000), D0 := ((823429826303571428511 : Rat) / 320000000000000000000), D1 := ((241837794303571428511 : Rat) / 320000000000000000000), D2 := ((4890626303571428511 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 32000000000000000000), D4 := ((182789773303571348247 : Rat) / 800000000000000000000), LB := ((1814479410057343 : Rat) / 125000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((823429826303571428511 : Rat) / 320000000000000000000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((47276054267857142273 : Rat) / 320000000000000000000), D4 := ((357428502767856982309 : Rat) / 1600000000000000000000), LB := ((14658131287373699 : Rat) / 2000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((165338048767857142837 : Rat) / 64000000000000000000), D0 := ((165338048767857142837 : Rat) / 64000000000000000000), D1 := ((49019642367857142837 : Rat) / 64000000000000000000), D2 := ((1630208767857142837 : Rat) / 64000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((87319364732142817031 : Rat) / 400000000000000000000), LB := ((4786477989655591 : Rat) / 2000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((165338048767857142837 : Rat) / 64000000000000000000), R := ((1655010696446428571207 : Rat) / 640000000000000000000), D0 := ((1655010696446428571207 : Rat) / 640000000000000000000), D1 := ((491826632446428571207 : Rat) / 640000000000000000000), D2 := ((17932296446428571207 : Rat) / 640000000000000000000), D3 := ((44015636732142856599 : Rat) / 320000000000000000000), D4 := ((341126415089285553939 : Rat) / 1600000000000000000000), LB := ((2968967062627781 : Rat) / 500000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1655010696446428571207 : Rat) / 640000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((86401064696428570361 : Rat) / 640000000000000000000), D4 := ((674101786339285393693 : Rat) / 3200000000000000000000), LB := ((113556075188731 : Rat) / 25000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((1658271113982142856881 : Rat) / 640000000000000000000), D0 := ((1658271113982142856881 : Rat) / 640000000000000000000), D1 := ((495087049982142856881 : Rat) / 640000000000000000000), D2 := ((21192713982142856881 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((166487685624999919877 : Rat) / 800000000000000000000), LB := ((173163145790739 : Rat) / 50000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1658271113982142856881 : Rat) / 640000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((83140647160714284687 : Rat) / 640000000000000000000), D4 := ((657799698660713965323 : Rat) / 3200000000000000000000), LB := ((26753127862894077 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((332306306303571428511 : Rat) / 128000000000000000000), D0 := ((332306306303571428511 : Rat) / 128000000000000000000), D1 := ((99669493503571428511 : Rat) / 128000000000000000000), D2 := ((4890626303571428511 : Rat) / 128000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((324824327410714125569 : Rat) / 1600000000000000000000), LB := ((10795511967551241 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((332306306303571428511 : Rat) / 128000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((79880229624999999013 : Rat) / 640000000000000000000), D4 := ((641497610982142536953 : Rat) / 3200000000000000000000), LB := ((9500809348230721 : Rat) / 5000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((1664791949053571428229 : Rat) / 640000000000000000000), D0 := ((1664791949053571428229 : Rat) / 640000000000000000000), D1 := ((501607885053571428229 : Rat) / 640000000000000000000), D2 := ((27713549053571428229 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((39584160446428551423 : Rat) / 200000000000000000000), LB := ((377551218118799 : Rat) / 200000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1664791949053571428229 : Rat) / 640000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((76619812089285713339 : Rat) / 640000000000000000000), D4 := ((625195523303571108583 : Rat) / 3200000000000000000000), LB := ((264264781767401 : Rat) / 125000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((308522239732142697199 : Rat) / 1600000000000000000000), LB := ((25738999447161293 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((608893435624999680213 : Rat) / 3200000000000000000000), LB := ((32637720769704837 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((150185597946428491507 : Rat) / 800000000000000000000), LB := ((836426744960983 : Rat) / 200000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((592591347946428251843 : Rat) / 3200000000000000000000), LB := ((666112506874289 : Rat) / 125000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((292220152053571268829 : Rat) / 1600000000000000000000), LB := ((12372814840927449 : Rat) / 10000000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((71017277053571388661 : Rat) / 400000000000000000000), LB := ((480896141053333 : Rat) / 100000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((275918064374999840459 : Rat) / 1600000000000000000000), LB := ((933081483117737 : Rat) / 100000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((133883510267857063137 : Rat) / 800000000000000000000), LB := ((467944181773583 : Rat) / 100000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((15716558303571418619 : Rat) / 100000000000000000000), LB := ((2420543221262117 : Rat) / 125000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((117581422589285634767 : Rat) / 800000000000000000000), LB := ((3919951598467897 : Rat) / 100000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((54715189374999960291 : Rat) / 400000000000000000000), LB := ((1175440837381661 : Rat) / 25000000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((23282072767857123053 : Rat) / 200000000000000000000), LB := ((1190808816564029 : Rat) / 12500000000000000) },
  { w1 := ((2057273042178649 : Rat) / 2000000000000000), w2 := ((5738575520482337 : Rat) / 200000000000000000), w3 := ((14683518859142447 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((138244395089285714401 : Rat) / 50000000000000000000), D0 := ((138244395089285714401 : Rat) / 50000000000000000000), D1 := ((47370640089285714401 : Rat) / 50000000000000000000), D2 := ((10347645089285714401 : Rat) / 50000000000000000000), D3 := ((274575156250000027 : Rat) / 6250000000000000000), D4 := ((3782757232142852217 : Rat) / 50000000000000000000), LB := ((15188369530105827 : Rat) / 10000000000000000000) }
]

def block269RightChunk000L : Rat := ((8823462053571428583 : Rat) / 5000000000000000000)
def block269RightChunk000R : Rat := ((138244395089285714401 : Rat) / 50000000000000000000)

def block269RightChunk000Certificate : Bool :=
  allBoxesValid block269RightChunk000 &&
  coversFromBool block269RightChunk000 block269RightChunk000L block269RightChunk000R

theorem block269RightChunk000Certificate_eq_true :
    block269RightChunk000Certificate = true := by
  native_decide

def block269RightChainCertificate : Bool :=
  decide (
    block269RightL = ((8823462053571428583 : Rat) / 5000000000000000000) /\
    ((138244395089285714401 : Rat) / 50000000000000000000) = block269RightR)

theorem block269RightChainCertificate_eq_true :
    block269RightChainCertificate = true := by
  native_decide

def block269LeftBoxCount : Nat := boxCount block269LeftBoxes
def block269RightBoxCount : Nat := 92

def block269_rational_certificate : Prop :=
    block269LeftCertificate = true /\
    block269RightChainCertificate = true /\
    block269RightChunk000Certificate = true

theorem block269_rational_certificate_proof :
    block269_rational_certificate := by
  exact ⟨block269LeftCertificate_eq_true, block269RightChainCertificate_eq_true, block269RightChunk000Certificate_eq_true⟩

end Block269
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block269

open Set

def block269W1 : Rat := ((2057273042178649 : Rat) / 2000000000000000)
def block269W2 : Rat := ((5738575520482337 : Rat) / 200000000000000000)
def block269W3 : Rat := ((14683518859142447 : Rat) / 50000000000000000)
def block269W4 : Rat := (0 : Rat)
def block269S1 : Rat := ((18174751 : Rat) / 10000000)
def block269S2 : Rat := ((511587 : Rat) / 200000)
def block269S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block269S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block269V (y : ℝ) : ℝ :=
  ratPotential block269W1 block269W2 block269W3 block269W4 block269S1 block269S2 block269S3 block269S4 y

def block269LeftParamsCertificate : Bool :=
  allBoxesSameParams block269LeftBoxes block269W1 block269W2 block269W3 block269W4 block269S1 block269S2 block269S3 block269S4

theorem block269LeftParamsCertificate_eq_true :
    block269LeftParamsCertificate = true := by
  native_decide

theorem block269_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block269LeftL : ℝ) (block269LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block269S1 : ℝ))
    (hy2ne : y ≠ (block269S2 : ℝ))
    (hy3ne : y ≠ (block269S3 : ℝ))
    (hy4ne : y ≠ (block269S4 : ℝ)) :
    0 < block269V y := by
  have hcert := block269LeftCertificate_eq_true
  unfold block269LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block269LeftBoxes) (lo := block269LeftL) (hi := block269LeftR)
    (w1 := block269W1) (w2 := block269W2) (w3 := block269W3) (w4 := block269W4)
    (s1 := block269S1) (s2 := block269S2) (s3 := block269S3) (s4 := block269S4)
    hboxes hcover block269LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block269RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block269RightChunk000 block269W1 block269W2 block269W3 block269W4 block269S1 block269S2 block269S3 block269S4

theorem block269RightChunk000ParamsCertificate_eq_true :
    block269RightChunk000ParamsCertificate = true := by
  native_decide

theorem block269_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block269RightChunk000L : ℝ) (block269RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block269S1 : ℝ))
    (hy2ne : y ≠ (block269S2 : ℝ))
    (hy3ne : y ≠ (block269S3 : ℝ))
    (hy4ne : y ≠ (block269S4 : ℝ)) :
    0 < block269V y := by
  have hcert := block269RightChunk000Certificate_eq_true
  unfold block269RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block269RightChunk000) (lo := block269RightChunk000L) (hi := block269RightChunk000R)
    (w1 := block269W1) (w2 := block269W2) (w3 := block269W3) (w4 := block269W4)
    (s1 := block269S1) (s2 := block269S2) (s3 := block269S3) (s4 := block269S4)
    hboxes hcover block269RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block269_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block269RightL : ℝ) (block269RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block269S1 : ℝ))
    (hy2ne : y ≠ (block269S2 : ℝ))
    (hy3ne : y ≠ (block269S3 : ℝ))
    (hy4ne : y ≠ (block269S4 : ℝ)) :
    0 < block269V y := by
  have hL : (block269RightChunk000L : ℝ) = (block269RightL : ℝ) := by
    norm_num [block269RightChunk000L, block269RightL]
  have hR : (block269RightChunk000R : ℝ) = (block269RightR : ℝ) := by
    norm_num [block269RightChunk000R, block269RightR]
  have hyc : y ∈ Icc (block269RightChunk000L : ℝ) (block269RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block269_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block269_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block269LeftL : ℝ) (block269LeftR : ℝ) →
    y ≠ 0 → y ≠ (block269S1 : ℝ) → y ≠ (block269S2 : ℝ) →
    y ≠ (block269S3 : ℝ) → y ≠ (block269S4 : ℝ) → 0 < block269V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block269RightL : ℝ) (block269RightR : ℝ) →
    y ≠ 0 → y ≠ (block269S1 : ℝ) → y ≠ (block269S2 : ℝ) →
    y ≠ (block269S3 : ℝ) → y ≠ (block269S4 : ℝ) → 0 < block269V y)

theorem block269_reallog_certificate_proof :
    block269_reallog_certificate := by
  exact ⟨block269_left_V_pos, block269_right_V_pos⟩

end Block269
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block269.block269V
#check Erdos1038Lean.M1817475.Block269.block269_left_V_pos
#check Erdos1038Lean.M1817475.Block269.block269_right_V_pos
#check Erdos1038Lean.M1817475.Block269.block269_reallog_certificate_proof
