/-
Self-contained Lean4Web paste file.
Block 10 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block010

def block010LeftL : Rat := ((40766229910714285719 : Rat) / 50000000000000000000)
def block010LeftR : Rat := ((4077600446428571429 : Rat) / 5000000000000000000)
def block010RightL : Rat := ((90766229910714285719 : Rat) / 50000000000000000000)
def block010RightR : Rat := ((14077600446428571429 : Rat) / 5000000000000000000)

def block010LeftBoxes : List RatBox := [
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((40766229910714285719 : Rat) / 50000000000000000000), R := ((4077600446428571429 : Rat) / 5000000000000000000), D0 := ((4077600446428571429 : Rat) / 5000000000000000000), D1 := ((50107525089285714281 : Rat) / 50000000000000000000), D2 := ((87130520089285714281 : Rat) / 50000000000000000000), D3 := ((92984543839285714281 : Rat) / 50000000000000000000), D4 := ((100804191696428566321 : Rat) / 50000000000000000000), LB := ((3121343053938519 : Rat) / 500000000000000000) }
]

def block010LeftCertificate : Bool :=
  allBoxesValid block010LeftBoxes &&
  coversFromBool block010LeftBoxes block010LeftL block010LeftR

theorem block010LeftCertificate_eq_true :
    block010LeftCertificate = true := by
  native_decide

def block010RightChunk000 : List RatBox := [
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((90766229910714285719 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((107525089285714281 : Rat) / 50000000000000000000), D2 := ((37130520089285714281 : Rat) / 50000000000000000000), D3 := ((42984543839285714281 : Rat) / 50000000000000000000), D4 := ((50804191696428566321 : Rat) / 50000000000000000000), LB := ((14223522040407369 : Rat) / 250000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((1267416665178571301 : Rat) / 1250000000000000000), LB := ((1934534998602221 : Rat) / 1000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((511587 : Rat) / 200000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((341841790178571301 : Rat) / 1250000000000000000), LB := ((407582802433349 : Rat) / 500000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((27452677821428571429 : Rat) / 10000000000000000000), D0 := ((27452677821428571429 : Rat) / 10000000000000000000), D1 := ((9277926821428571429 : Rat) / 10000000000000000000), D2 := ((1873327821428571429 : Rat) / 10000000000000000000), D3 := ((702523071428571429 : Rat) / 10000000000000000000), D4 := ((195491196428571301 : Rat) / 1250000000000000000), LB := ((8822266429095721 : Rat) / 50000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((27452677821428571429 : Rat) / 10000000000000000000), R := ((22102646871428571429 : Rat) / 8000000000000000000), D0 := ((22102646871428571429 : Rat) / 8000000000000000000), D1 := ((7562846071428571429 : Rat) / 8000000000000000000), D2 := ((1639166871428571429 : Rat) / 8000000000000000000), D3 := ((702523071428571429 : Rat) / 8000000000000000000), D4 := ((861406499999998979 : Rat) / 10000000000000000000), LB := ((56461608614977 : Rat) / 400000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((22102646871428571429 : Rat) / 8000000000000000000), R := ((55607878714285714287 : Rat) / 20000000000000000000), D0 := ((55607878714285714287 : Rat) / 20000000000000000000), D1 := ((19258376714285714287 : Rat) / 20000000000000000000), D2 := ((4449178714285714287 : Rat) / 20000000000000000000), D3 := ((2107569214285714287 : Rat) / 20000000000000000000), D4 := ((2743102928571424487 : Rat) / 40000000000000000000), LB := ((8077399921397499 : Rat) / 500000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((55607878714285714287 : Rat) / 20000000000000000000), R := ((223134037928571428577 : Rat) / 80000000000000000000), D0 := ((223134037928571428577 : Rat) / 80000000000000000000), D1 := ((77736029928571428577 : Rat) / 80000000000000000000), D2 := ((18499237928571428577 : Rat) / 80000000000000000000), D3 := ((9132799928571428577 : Rat) / 80000000000000000000), D4 := ((1020289928571426529 : Rat) / 20000000000000000000), LB := ((4040556276768137 : Rat) / 5000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((223134037928571428577 : Rat) / 80000000000000000000), R := ((446970598928571428583 : Rat) / 160000000000000000000), D0 := ((446970598928571428583 : Rat) / 160000000000000000000), D1 := ((156174582928571428583 : Rat) / 160000000000000000000), D2 := ((37700998928571428583 : Rat) / 160000000000000000000), D3 := ((18968122928571428583 : Rat) / 160000000000000000000), D4 := ((3378636642857134687 : Rat) / 80000000000000000000), LB := ((7569468255419931 : Rat) / 2000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((446970598928571428583 : Rat) / 160000000000000000000), R := ((178928744185714285719 : Rat) / 64000000000000000000), D0 := ((178928744185714285719 : Rat) / 64000000000000000000), D1 := ((62610337785714285719 : Rat) / 64000000000000000000), D2 := ((15220904185714285719 : Rat) / 64000000000000000000), D3 := ((7727753785714285719 : Rat) / 64000000000000000000), D4 := ((1210950042857139589 : Rat) / 32000000000000000000), LB := ((2304286124869187 : Rat) / 250000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((178928744185714285719 : Rat) / 64000000000000000000), R := ((111918280500000000003 : Rat) / 40000000000000000000), D0 := ((111918280500000000003 : Rat) / 40000000000000000000), D1 := ((39219276500000000003 : Rat) / 40000000000000000000), D2 := ((9600880500000000003 : Rat) / 40000000000000000000), D3 := ((4917661500000000003 : Rat) / 40000000000000000000), D4 := ((11406977357142824461 : Rat) / 320000000000000000000), LB := ((2065223062439503 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((111918280500000000003 : Rat) / 40000000000000000000), R := ((1791395011071428571477 : Rat) / 640000000000000000000), D0 := ((1791395011071428571477 : Rat) / 640000000000000000000), D1 := ((628210947071428571477 : Rat) / 640000000000000000000), D2 := ((154316611071428571477 : Rat) / 640000000000000000000), D3 := ((79385107071428571477 : Rat) / 640000000000000000000), D4 := ((1338056785714281629 : Rat) / 40000000000000000000), LB := ((7015989923016663 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1791395011071428571477 : Rat) / 640000000000000000000), R := ((896048767071428571453 : Rat) / 320000000000000000000), D0 := ((896048767071428571453 : Rat) / 320000000000000000000), D1 := ((314456735071428571453 : Rat) / 320000000000000000000), D2 := ((77509567071428571453 : Rat) / 320000000000000000000), D3 := ((40043815071428571453 : Rat) / 320000000000000000000), D4 := ((4141277099999986927 : Rat) / 128000000000000000000), LB := ((4350094117495873 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((896048767071428571453 : Rat) / 320000000000000000000), R := ((358560011442857142867 : Rat) / 128000000000000000000), D0 := ((358560011442857142867 : Rat) / 128000000000000000000), D1 := ((125923198642857142867 : Rat) / 128000000000000000000), D2 := ((31144331442857142867 : Rat) / 128000000000000000000), D3 := ((16158030642857142867 : Rat) / 128000000000000000000), D4 := ((10001931214285681603 : Rat) / 320000000000000000000), LB := ((496810643299761 : Rat) / 250000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((358560011442857142867 : Rat) / 128000000000000000000), R := ((3586302637500000000099 : Rat) / 1280000000000000000000), D0 := ((3586302637500000000099 : Rat) / 1280000000000000000000), D1 := ((1259934509500000000099 : Rat) / 1280000000000000000000), D2 := ((312145837500000000099 : Rat) / 1280000000000000000000), D3 := ((162282829500000000099 : Rat) / 1280000000000000000000), D4 := ((19301339357142791777 : Rat) / 640000000000000000000), LB := ((10963353504401363 : Rat) / 2000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3586302637500000000099 : Rat) / 1280000000000000000000), R := ((448375645071428571441 : Rat) / 160000000000000000000), D0 := ((448375645071428571441 : Rat) / 160000000000000000000), D1 := ((157579629071428571441 : Rat) / 160000000000000000000), D2 := ((39106045071428571441 : Rat) / 160000000000000000000), D3 := ((20373169071428571441 : Rat) / 160000000000000000000), D4 := ((303201245142856097 : Rat) / 10240000000000000000), LB := ((2293851531711577 : Rat) / 500000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((448375645071428571441 : Rat) / 160000000000000000000), R := ((3587707683642857142957 : Rat) / 1280000000000000000000), D0 := ((3587707683642857142957 : Rat) / 1280000000000000000000), D1 := ((1261339555642857142957 : Rat) / 1280000000000000000000), D2 := ((313550883642857142957 : Rat) / 1280000000000000000000), D3 := ((163687875642857142957 : Rat) / 1280000000000000000000), D4 := ((4649704071428555087 : Rat) / 160000000000000000000), LB := ((3783549146179399 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3587707683642857142957 : Rat) / 1280000000000000000000), R := ((1794205103357142857193 : Rat) / 640000000000000000000), D0 := ((1794205103357142857193 : Rat) / 640000000000000000000), D1 := ((631021039357142857193 : Rat) / 640000000000000000000), D2 := ((157126703357142857193 : Rat) / 640000000000000000000), D3 := ((82195199357142857193 : Rat) / 640000000000000000000), D4 := ((36495109499999869267 : Rat) / 1280000000000000000000), LB := ((3072522157448243 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1794205103357142857193 : Rat) / 640000000000000000000), R := ((717822545957142857163 : Rat) / 256000000000000000000), D0 := ((717822545957142857163 : Rat) / 256000000000000000000), D1 := ((252548920357142857163 : Rat) / 256000000000000000000), D2 := ((62991185957142857163 : Rat) / 256000000000000000000), D3 := ((33018584357142857163 : Rat) / 256000000000000000000), D4 := ((17896293214285648919 : Rat) / 640000000000000000000), LB := ((1229061157431599 : Rat) / 500000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((717822545957142857163 : Rat) / 256000000000000000000), R := ((897453813214285714311 : Rat) / 320000000000000000000), D0 := ((897453813214285714311 : Rat) / 320000000000000000000), D1 := ((315861781214285714311 : Rat) / 320000000000000000000), D2 := ((78914613214285714311 : Rat) / 320000000000000000000), D3 := ((41448861214285714311 : Rat) / 320000000000000000000), D4 := ((35090063357142726409 : Rat) / 1280000000000000000000), LB := ((19440582042951071 : Rat) / 10000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((897453813214285714311 : Rat) / 320000000000000000000), R := ((3590517775928571428673 : Rat) / 1280000000000000000000), D0 := ((3590517775928571428673 : Rat) / 1280000000000000000000), D1 := ((1264149647928571428673 : Rat) / 1280000000000000000000), D2 := ((316360975928571428673 : Rat) / 1280000000000000000000), D3 := ((166497967928571428673 : Rat) / 1280000000000000000000), D4 := ((1719377014285707749 : Rat) / 64000000000000000000), LB := ((1534263634784483 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3590517775928571428673 : Rat) / 1280000000000000000000), R := ((1795610149500000000051 : Rat) / 640000000000000000000), D0 := ((1795610149500000000051 : Rat) / 640000000000000000000), D1 := ((632426085500000000051 : Rat) / 640000000000000000000), D2 := ((158531749500000000051 : Rat) / 640000000000000000000), D3 := ((83600245500000000051 : Rat) / 640000000000000000000), D4 := ((33685017214285583551 : Rat) / 1280000000000000000000), LB := ((3082290580594671 : Rat) / 2500000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1795610149500000000051 : Rat) / 640000000000000000000), R := ((3591922822071428571531 : Rat) / 1280000000000000000000), D0 := ((3591922822071428571531 : Rat) / 1280000000000000000000), D1 := ((1265554694071428571531 : Rat) / 1280000000000000000000), D2 := ((317766022071428571531 : Rat) / 1280000000000000000000), D3 := ((167903014071428571531 : Rat) / 1280000000000000000000), D4 := ((16491247071428506061 : Rat) / 640000000000000000000), LB := ((5222289956771653 : Rat) / 5000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3591922822071428571531 : Rat) / 1280000000000000000000), R := ((44907816814285714287 : Rat) / 16000000000000000000), D0 := ((44907816814285714287 : Rat) / 16000000000000000000), D1 := ((15828215214285714287 : Rat) / 16000000000000000000), D2 := ((3980856814285714287 : Rat) / 16000000000000000000), D3 := ((2107569214285714287 : Rat) / 16000000000000000000), D4 := ((32279971071428440693 : Rat) / 1280000000000000000000), LB := ((4868090191077479 : Rat) / 5000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((44907816814285714287 : Rat) / 16000000000000000000), R := ((3593327868214285714389 : Rat) / 1280000000000000000000), D0 := ((3593327868214285714389 : Rat) / 1280000000000000000000), D1 := ((1266959740214285714389 : Rat) / 1280000000000000000000), D2 := ((319171068214285714389 : Rat) / 1280000000000000000000), D3 := ((169308060214285714389 : Rat) / 1280000000000000000000), D4 := ((1973590499999991829 : Rat) / 80000000000000000000), LB := ((10254378945977471 : Rat) / 10000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3593327868214285714389 : Rat) / 1280000000000000000000), R := ((1797015195642857142909 : Rat) / 640000000000000000000), D0 := ((1797015195642857142909 : Rat) / 640000000000000000000), D1 := ((633831131642857142909 : Rat) / 640000000000000000000), D2 := ((159936795642857142909 : Rat) / 640000000000000000000), D3 := ((85005291642857142909 : Rat) / 640000000000000000000), D4 := ((6174984985714259567 : Rat) / 256000000000000000000), LB := ((1205299580557151 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1797015195642857142909 : Rat) / 640000000000000000000), R := ((3594732914357142857247 : Rat) / 1280000000000000000000), D0 := ((3594732914357142857247 : Rat) / 1280000000000000000000), D1 := ((1268364786357142857247 : Rat) / 1280000000000000000000), D2 := ((320576114357142857247 : Rat) / 1280000000000000000000), D3 := ((170713106357142857247 : Rat) / 1280000000000000000000), D4 := ((15086200928571363203 : Rat) / 640000000000000000000), LB := ((3037913891275057 : Rat) / 2000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3594732914357142857247 : Rat) / 1280000000000000000000), R := ((898858859357142857169 : Rat) / 320000000000000000000), D0 := ((898858859357142857169 : Rat) / 320000000000000000000), D1 := ((317266827357142857169 : Rat) / 320000000000000000000), D2 := ((80319659357142857169 : Rat) / 320000000000000000000), D3 := ((42853907357142857169 : Rat) / 320000000000000000000), D4 := ((29469878785714154977 : Rat) / 1280000000000000000000), LB := ((1972570682686303 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((898858859357142857169 : Rat) / 320000000000000000000), R := ((719227592100000000021 : Rat) / 256000000000000000000), D0 := ((719227592100000000021 : Rat) / 256000000000000000000), D1 := ((253953966500000000021 : Rat) / 256000000000000000000), D2 := ((64396232100000000021 : Rat) / 256000000000000000000), D3 := ((34423630500000000021 : Rat) / 256000000000000000000), D4 := ((7191838928571395887 : Rat) / 320000000000000000000), LB := ((12863737770180683 : Rat) / 5000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((719227592100000000021 : Rat) / 256000000000000000000), R := ((1798420241785714285767 : Rat) / 640000000000000000000), D0 := ((1798420241785714285767 : Rat) / 640000000000000000000), D1 := ((635236177785714285767 : Rat) / 640000000000000000000), D2 := ((161341841785714285767 : Rat) / 640000000000000000000), D3 := ((86410337785714285767 : Rat) / 640000000000000000000), D4 := ((28064832642857012119 : Rat) / 1280000000000000000000), LB := ((3326584450060621 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1798420241785714285767 : Rat) / 640000000000000000000), R := ((3597543006642857142963 : Rat) / 1280000000000000000000), D0 := ((3597543006642857142963 : Rat) / 1280000000000000000000), D1 := ((1271174878642857142963 : Rat) / 1280000000000000000000), D2 := ((323386206642857142963 : Rat) / 1280000000000000000000), D3 := ((173523198642857142963 : Rat) / 1280000000000000000000), D4 := ((2736230957142844069 : Rat) / 128000000000000000000), LB := ((265107375510637 : Rat) / 62500000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3597543006642857142963 : Rat) / 1280000000000000000000), R := ((449780691214285714299 : Rat) / 160000000000000000000), D0 := ((449780691214285714299 : Rat) / 160000000000000000000), D1 := ((158984675214285714299 : Rat) / 160000000000000000000), D2 := ((40511091214285714299 : Rat) / 160000000000000000000), D3 := ((21778215214285714299 : Rat) / 160000000000000000000), D4 := ((26659786499999869261 : Rat) / 1280000000000000000000), LB := ((2663190325059517 : Rat) / 500000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((449780691214285714299 : Rat) / 160000000000000000000), R := ((14398602303428571429 : Rat) / 5120000000000000000), D0 := ((14398602303428571429 : Rat) / 5120000000000000000), D1 := ((5093129791428571429 : Rat) / 5120000000000000000), D2 := ((1301975103428571429 : Rat) / 5120000000000000000), D3 := ((702523071428571429 : Rat) / 5120000000000000000), D4 := ((3244657928571412229 : Rat) / 160000000000000000000), LB := ((5548575927090127 : Rat) / 5000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((14398602303428571429 : Rat) / 5120000000000000000), R := ((900263905500000000027 : Rat) / 320000000000000000000), D0 := ((900263905500000000027 : Rat) / 320000000000000000000), D1 := ((318671873500000000027 : Rat) / 320000000000000000000), D2 := ((81724705500000000027 : Rat) / 320000000000000000000), D3 := ((44258953500000000027 : Rat) / 320000000000000000000), D4 := ((12276108642857077487 : Rat) / 640000000000000000000), LB := ((2108176356515501 : Rat) / 500000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((900263905500000000027 : Rat) / 320000000000000000000), R := ((1801230334071428571483 : Rat) / 640000000000000000000), D0 := ((1801230334071428571483 : Rat) / 640000000000000000000), D1 := ((638046270071428571483 : Rat) / 640000000000000000000), D2 := ((164151934071428571483 : Rat) / 640000000000000000000), D3 := ((89220430071428571483 : Rat) / 640000000000000000000), D4 := ((5786792785714253029 : Rat) / 320000000000000000000), LB := ((8163290285246871 : Rat) / 1000000000000000000) },
  { w1 := ((9575327037577903 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2526066277374633 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1801230334071428571483 : Rat) / 640000000000000000000), R := ((14077600446428571429 : Rat) / 5000000000000000000), D0 := ((14077600446428571429 : Rat) / 5000000000000000000), D1 := ((4990224946428571429 : Rat) / 5000000000000000000), D2 := ((1287925446428571429 : Rat) / 5000000000000000000), D3 := ((702523071428571429 : Rat) / 5000000000000000000), D4 := ((10871062499999934629 : Rat) / 640000000000000000000), LB := ((13054227480148617 : Rat) / 1000000000000000000) }
]

def block010RightChunk000L : Rat := ((90766229910714285719 : Rat) / 50000000000000000000)
def block010RightChunk000R : Rat := ((14077600446428571429 : Rat) / 5000000000000000000)

def block010RightChunk000Certificate : Bool :=
  allBoxesValid block010RightChunk000 &&
  coversFromBool block010RightChunk000 block010RightChunk000L block010RightChunk000R

theorem block010RightChunk000Certificate_eq_true :
    block010RightChunk000Certificate = true := by
  native_decide

def block010RightChainCertificate : Bool :=
  decide (
    block010RightL = ((90766229910714285719 : Rat) / 50000000000000000000) /\
    ((14077600446428571429 : Rat) / 5000000000000000000) = block010RightR)

theorem block010RightChainCertificate_eq_true :
    block010RightChainCertificate = true := by
  native_decide

def block010LeftBoxCount : Nat := boxCount block010LeftBoxes
def block010RightBoxCount : Nat := 35

def block010_rational_certificate : Prop :=
    block010LeftCertificate = true /\
    block010RightChainCertificate = true /\
    block010RightChunk000Certificate = true

theorem block010_rational_certificate_proof :
    block010_rational_certificate := by
  exact ⟨block010LeftCertificate_eq_true, block010RightChainCertificate_eq_true, block010RightChunk000Certificate_eq_true⟩

end Block010
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block010

open Set

def block010W1 : Rat := ((9575327037577903 : Rat) / 1000000000000000)
def block010W2 : Rat := (0 : Rat)
def block010W3 : Rat := (0 : Rat)
def block010W4 : Rat := ((2526066277374633 : Rat) / 10000000000000000)
def block010S1 : Rat := ((18174751 : Rat) / 10000000)
def block010S2 : Rat := ((511587 : Rat) / 200000)
def block010S3 : Rat := ((107000619 : Rat) / 40000000)
def block010S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block010V (y : ℝ) : ℝ :=
  ratPotential block010W1 block010W2 block010W3 block010W4 block010S1 block010S2 block010S3 block010S4 y

def block010LeftParamsCertificate : Bool :=
  allBoxesSameParams block010LeftBoxes block010W1 block010W2 block010W3 block010W4 block010S1 block010S2 block010S3 block010S4

theorem block010LeftParamsCertificate_eq_true :
    block010LeftParamsCertificate = true := by
  native_decide

theorem block010_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block010LeftL : ℝ) (block010LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block010S1 : ℝ))
    (hy2ne : y ≠ (block010S2 : ℝ))
    (hy3ne : y ≠ (block010S3 : ℝ))
    (hy4ne : y ≠ (block010S4 : ℝ)) :
    0 < block010V y := by
  have hcert := block010LeftCertificate_eq_true
  unfold block010LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block010LeftBoxes) (lo := block010LeftL) (hi := block010LeftR)
    (w1 := block010W1) (w2 := block010W2) (w3 := block010W3) (w4 := block010W4)
    (s1 := block010S1) (s2 := block010S2) (s3 := block010S3) (s4 := block010S4)
    hboxes hcover block010LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block010RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block010RightChunk000 block010W1 block010W2 block010W3 block010W4 block010S1 block010S2 block010S3 block010S4

theorem block010RightChunk000ParamsCertificate_eq_true :
    block010RightChunk000ParamsCertificate = true := by
  native_decide

theorem block010_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block010RightChunk000L : ℝ) (block010RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block010S1 : ℝ))
    (hy2ne : y ≠ (block010S2 : ℝ))
    (hy3ne : y ≠ (block010S3 : ℝ))
    (hy4ne : y ≠ (block010S4 : ℝ)) :
    0 < block010V y := by
  have hcert := block010RightChunk000Certificate_eq_true
  unfold block010RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block010RightChunk000) (lo := block010RightChunk000L) (hi := block010RightChunk000R)
    (w1 := block010W1) (w2 := block010W2) (w3 := block010W3) (w4 := block010W4)
    (s1 := block010S1) (s2 := block010S2) (s3 := block010S3) (s4 := block010S4)
    hboxes hcover block010RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block010_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block010RightL : ℝ) (block010RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block010S1 : ℝ))
    (hy2ne : y ≠ (block010S2 : ℝ))
    (hy3ne : y ≠ (block010S3 : ℝ))
    (hy4ne : y ≠ (block010S4 : ℝ)) :
    0 < block010V y := by
  have hL : (block010RightChunk000L : ℝ) = (block010RightL : ℝ) := by
    norm_num [block010RightChunk000L, block010RightL]
  have hR : (block010RightChunk000R : ℝ) = (block010RightR : ℝ) := by
    norm_num [block010RightChunk000R, block010RightR]
  have hyc : y ∈ Icc (block010RightChunk000L : ℝ) (block010RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block010_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block010_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block010LeftL : ℝ) (block010LeftR : ℝ) →
    y ≠ 0 → y ≠ (block010S1 : ℝ) → y ≠ (block010S2 : ℝ) →
    y ≠ (block010S3 : ℝ) → y ≠ (block010S4 : ℝ) → 0 < block010V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block010RightL : ℝ) (block010RightR : ℝ) →
    y ≠ 0 → y ≠ (block010S1 : ℝ) → y ≠ (block010S2 : ℝ) →
    y ≠ (block010S3 : ℝ) → y ≠ (block010S4 : ℝ) → 0 < block010V y)

theorem block010_reallog_certificate_proof :
    block010_reallog_certificate := by
  exact ⟨block010_left_V_pos, block010_right_V_pos⟩

end Block010
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block010.block010V
#check Erdos1038Lean.M1817475.Block010.block010_left_V_pos
#check Erdos1038Lean.M1817475.Block010.block010_right_V_pos
#check Erdos1038Lean.M1817475.Block010.block010_reallog_certificate_proof
