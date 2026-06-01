/-
Self-contained Lean4Web paste file.
Block 342 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block342

def block342LeftL : Rat := ((37521078125000000147 : Rat) / 50000000000000000000)
def block342LeftR : Rat := ((18765426339285714359 : Rat) / 25000000000000000000)
def block342RightL : Rat := ((87521078125000000147 : Rat) / 50000000000000000000)
def block342RightR : Rat := ((68765426339285714359 : Rat) / 25000000000000000000)

def block342LeftBoxes : List RatBox := [
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37521078125000000147 : Rat) / 50000000000000000000), R := ((18765426339285714359 : Rat) / 25000000000000000000), D0 := ((18765426339285714359 : Rat) / 25000000000000000000), D1 := ((53352676874999999853 : Rat) / 50000000000000000000), D2 := ((90375671874999999853 : Rat) / 50000000000000000000), D3 := ((11990835558035714269 : Rat) / 6250000000000000000), D4 := ((101097428303571423451 : Rat) / 50000000000000000000), LB := ((3168717982562387 : Rat) / 500000000000000000) }
]

def block342LeftCertificate : Bool :=
  allBoxesValid block342LeftBoxes &&
  coversFromBool block342LeftBoxes block342LeftL block342LeftR

theorem block342LeftCertificate_eq_true :
    block342LeftCertificate = true := by
  native_decide

def block342RightChunk000 : List RatBox := [
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87521078125000000147 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3352676874999999853 : Rat) / 50000000000000000000), D2 := ((40375671874999999853 : Rat) / 50000000000000000000), D3 := ((5740835558035714269 : Rat) / 6250000000000000000), D4 := ((51097428303571423451 : Rat) / 50000000000000000000), LB := ((19173649881077939 : Rat) / 10000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42574007589285714299 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((8941475449392139 : Rat) / 50000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24062510089285714299 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((5773269920754547 : Rat) / 50000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19434635714285714299 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((3803596142181541 : Rat) / 50000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17120698526785714299 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((1687206370810139 : Rat) / 100000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14806761339285714299 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((82228402648227 : Rat) / 5000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13649792745535714299 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((9912189945895683 : Rat) / 500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((13071308448660714299 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((5632622925392669 : Rat) / 500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12492824151785714299 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((472253948912333 : Rat) / 125000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11914339854910714299 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((1679265100931343 : Rat) / 200000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11625097706473214299 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((1119448986202487 : Rat) / 200000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11335855558035714299 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((3902807805099863 : Rat) / 1250000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11046613409598214299 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((2467603163951379 : Rat) / 2500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10757371261160714299 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((2277513926608299 : Rat) / 500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10612750186941964299 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((473341207713477 : Rat) / 125000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10468129112723214299 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((3895086217880657 : Rat) / 1250000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10323508038504464299 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((509231859501047 : Rat) / 200000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10178886964285714299 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((2080367945197753 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10034265890066964299 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((17223451761592123 : Rat) / 10000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9889644815848214299 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((7380289617023861 : Rat) / 5000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9745023741629464299 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((6729145163779787 : Rat) / 5000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9600402667410714299 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((13363831516823577 : Rat) / 10000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9455781593191964299 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((14529006981297277 : Rat) / 10000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9311160518973214299 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((1701081714613667 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9166539444754464299 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((20872219060946717 : Rat) / 10000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9021918370535714299 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((6545759535604781 : Rat) / 2500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8877297296316964299 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((3302106957303097 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8732676222098214299 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((1658936781169007 : Rat) / 400000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8588055147879464299 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((5163815271514521 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8443434073660714299 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((13198165196080247 : Rat) / 10000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8154191925223214299 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((4352147585922339 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7864949776785714299 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((8292327615893103 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7575707628348214299 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((13313667523671857 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7286465479910714299 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1980605068785829 : Rat) / 200000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6707981183035714299 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((4701226860910693 : Rat) / 500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028725012589285714299 : Rat) / 400000000000000000000), D0 := ((1028725012589285714299 : Rat) / 400000000000000000000), D1 := ((301734972589285714299 : Rat) / 400000000000000000000), D2 := ((5551012589285714299 : Rat) / 400000000000000000000), D3 := ((5551012589285714299 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((3310407862547049 : Rat) / 62500000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028725012589285714299 : Rat) / 400000000000000000000), R := ((517138012589285714299 : Rat) / 200000000000000000000), D0 := ((517138012589285714299 : Rat) / 200000000000000000000), D1 := ((153642992589285714299 : Rat) / 200000000000000000000), D2 := ((5551012589285714299 : Rat) / 200000000000000000000), D3 := ((38857088125000000093 : Rat) / 400000000000000000000), D4 := ((16044607767857134897 : Rat) / 80000000000000000000), LB := ((13353978220981763 : Rat) / 500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517138012589285714299 : Rat) / 200000000000000000000), R := ((1039827037767857142897 : Rat) / 400000000000000000000), D0 := ((1039827037767857142897 : Rat) / 400000000000000000000), D1 := ((312836997767857142897 : Rat) / 400000000000000000000), D2 := ((16653037767857142897 : Rat) / 400000000000000000000), D3 := ((16653037767857142897 : Rat) / 200000000000000000000), D4 := ((37336013124999980093 : Rat) / 200000000000000000000), LB := ((9049924881286073 : Rat) / 500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1039827037767857142897 : Rat) / 400000000000000000000), R := ((261344512589285714299 : Rat) / 100000000000000000000), D0 := ((261344512589285714299 : Rat) / 100000000000000000000), D1 := ((79597002589285714299 : Rat) / 100000000000000000000), D2 := ((5551012589285714299 : Rat) / 100000000000000000000), D3 := ((5551012589285714299 : Rat) / 80000000000000000000), D4 := ((69121013660714245887 : Rat) / 400000000000000000000), LB := ((2029051175646271 : Rat) / 100000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261344512589285714299 : Rat) / 100000000000000000000), R := ((528240037767857142897 : Rat) / 200000000000000000000), D0 := ((528240037767857142897 : Rat) / 200000000000000000000), D1 := ((164745017767857142897 : Rat) / 200000000000000000000), D2 := ((16653037767857142897 : Rat) / 200000000000000000000), D3 := ((5551012589285714299 : Rat) / 100000000000000000000), D4 := ((15892500267857132897 : Rat) / 100000000000000000000), LB := ((3132370763795689 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528240037767857142897 : Rat) / 200000000000000000000), R := ((133447762589285714299 : Rat) / 50000000000000000000), D0 := ((133447762589285714299 : Rat) / 50000000000000000000), D1 := ((42574007589285714299 : Rat) / 50000000000000000000), D2 := ((5551012589285714299 : Rat) / 50000000000000000000), D3 := ((5551012589285714299 : Rat) / 200000000000000000000), D4 := ((5246797589285710299 : Rat) / 40000000000000000000), LB := ((7658987203789813 : Rat) / 100000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133447762589285714299 : Rat) / 50000000000000000000), R := ((107574828089285714323 : Rat) / 40000000000000000000), D0 := ((107574828089285714323 : Rat) / 40000000000000000000), D1 := ((34875824089285714323 : Rat) / 40000000000000000000), D2 := ((5257428089285714323 : Rat) / 40000000000000000000), D3 := ((4083090089285714419 : Rat) / 200000000000000000000), D4 := ((5170743839285709299 : Rat) / 50000000000000000000), LB := ((2337816779977433 : Rat) / 20000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((107574828089285714323 : Rat) / 40000000000000000000), R := ((270978615267857143017 : Rat) / 100000000000000000000), D0 := ((270978615267857143017 : Rat) / 100000000000000000000), D1 := ((89231105267857143017 : Rat) / 100000000000000000000), D2 := ((15185115267857143017 : Rat) / 100000000000000000000), D3 := ((4083090089285714419 : Rat) / 100000000000000000000), D4 := ((16599885267857122777 : Rat) / 200000000000000000000), LB := ((4830445570094599 : Rat) / 500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((270978615267857143017 : Rat) / 100000000000000000000), R := ((434382402446428571711 : Rat) / 160000000000000000000), D0 := ((434382402446428571711 : Rat) / 160000000000000000000), D1 := ((143586386446428571711 : Rat) / 160000000000000000000), D2 := ((25112802446428571711 : Rat) / 160000000000000000000), D3 := ((36747810803571429771 : Rat) / 800000000000000000000), D4 := ((6258397589285704179 : Rat) / 100000000000000000000), LB := ((2252320223088311 : Rat) / 100000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((434382402446428571711 : Rat) / 160000000000000000000), R := ((1087997551160714286487 : Rat) / 400000000000000000000), D0 := ((1087997551160714286487 : Rat) / 400000000000000000000), D1 := ((361007511160714286487 : Rat) / 400000000000000000000), D2 := ((64823551160714286487 : Rat) / 400000000000000000000), D3 := ((4083090089285714419 : Rat) / 80000000000000000000), D4 := ((45984090624999919013 : Rat) / 800000000000000000000), LB := ((5069715743609593 : Rat) / 500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1087997551160714286487 : Rat) / 400000000000000000000), R := ((2180078192410714287393 : Rat) / 800000000000000000000), D0 := ((2180078192410714287393 : Rat) / 800000000000000000000), D1 := ((726098112410714287393 : Rat) / 800000000000000000000), D2 := ((133730192410714287393 : Rat) / 800000000000000000000), D3 := ((44913990982142858609 : Rat) / 800000000000000000000), D4 := ((20950500267857102297 : Rat) / 400000000000000000000), LB := ((1000787005913939 : Rat) / 2500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2180078192410714287393 : Rat) / 800000000000000000000), R := ((872847894982142857841 : Rat) / 320000000000000000000), D0 := ((872847894982142857841 : Rat) / 320000000000000000000), D1 := ((291255862982142857841 : Rat) / 320000000000000000000), D2 := ((54308694982142857841 : Rat) / 320000000000000000000), D3 := ((93911072053571431637 : Rat) / 1600000000000000000000), D4 := ((1512716417857139607 : Rat) / 32000000000000000000), LB := ((37431779778897 : Rat) / 10000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((872847894982142857841 : Rat) / 320000000000000000000), R := ((546040320625000000453 : Rat) / 200000000000000000000), D0 := ((546040320625000000453 : Rat) / 200000000000000000000), D1 := ((182545300625000000453 : Rat) / 200000000000000000000), D2 := ((34453320625000000453 : Rat) / 200000000000000000000), D3 := ((12249270267857143257 : Rat) / 200000000000000000000), D4 := ((71552730803571265931 : Rat) / 1600000000000000000000), LB := ((9085193947270809 : Rat) / 10000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546040320625000000453 : Rat) / 200000000000000000000), R := ((8740728220089285721667 : Rat) / 3200000000000000000000), D0 := ((8740728220089285721667 : Rat) / 3200000000000000000000), D1 := ((2924807900089285721667 : Rat) / 3200000000000000000000), D2 := ((555336220089285721667 : Rat) / 3200000000000000000000), D3 := ((200071414375000006531 : Rat) / 3200000000000000000000), D4 := ((8433705089285693939 : Rat) / 200000000000000000000), LB := ((7727240637186883 : Rat) / 2000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8740728220089285721667 : Rat) / 3200000000000000000000), R := ((4372405655089285718043 : Rat) / 1600000000000000000000), D0 := ((4372405655089285718043 : Rat) / 1600000000000000000000), D1 := ((1464445495089285718043 : Rat) / 1600000000000000000000), D2 := ((279709655089285718043 : Rat) / 1600000000000000000000), D3 := ((4083090089285714419 : Rat) / 64000000000000000000), D4 := ((26171238267857077721 : Rat) / 640000000000000000000), LB := ((1210350143829797 : Rat) / 400000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4372405655089285718043 : Rat) / 1600000000000000000000), R := ((1749778880053571430101 : Rat) / 640000000000000000000), D0 := ((1749778880053571430101 : Rat) / 640000000000000000000), D1 := ((586594816053571430101 : Rat) / 640000000000000000000), D2 := ((112700480053571430101 : Rat) / 640000000000000000000), D3 := ((208237594553571435369 : Rat) / 3200000000000000000000), D4 := ((63386550624999837093 : Rat) / 1600000000000000000000), LB := ((11927351551520027 : Rat) / 5000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1749778880053571430101 : Rat) / 640000000000000000000), R := ((2188244372589285716231 : Rat) / 800000000000000000000), D0 := ((2188244372589285716231 : Rat) / 800000000000000000000), D1 := ((734264292589285716231 : Rat) / 800000000000000000000), D2 := ((141896372589285716231 : Rat) / 800000000000000000000), D3 := ((53080171160714287447 : Rat) / 800000000000000000000), D4 := ((122690011160713959767 : Rat) / 3200000000000000000000), LB := ((9744320467988121 : Rat) / 5000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2188244372589285716231 : Rat) / 800000000000000000000), R := ((8757060580446428579343 : Rat) / 3200000000000000000000), D0 := ((8757060580446428579343 : Rat) / 3200000000000000000000), D1 := ((2941140260446428579343 : Rat) / 3200000000000000000000), D2 := ((571668580446428579343 : Rat) / 3200000000000000000000), D3 := ((216403774732142864207 : Rat) / 3200000000000000000000), D4 := ((29651730267857061337 : Rat) / 800000000000000000000), LB := ((2154423261235619 : Rat) / 1250000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8757060580446428579343 : Rat) / 3200000000000000000000), R := ((4380571835267857146881 : Rat) / 1600000000000000000000), D0 := ((4380571835267857146881 : Rat) / 1600000000000000000000), D1 := ((1472611675267857146881 : Rat) / 1600000000000000000000), D2 := ((287875835267857146881 : Rat) / 1600000000000000000000), D3 := ((110243432410714289313 : Rat) / 1600000000000000000000), D4 := ((114523830982142530929 : Rat) / 3200000000000000000000), LB := ((1718113984075953 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4380571835267857146881 : Rat) / 1600000000000000000000), R := ((8765226760625000008181 : Rat) / 3200000000000000000000), D0 := ((8765226760625000008181 : Rat) / 3200000000000000000000), D1 := ((2949306440625000008181 : Rat) / 3200000000000000000000), D2 := ((579834760625000008181 : Rat) / 3200000000000000000000), D3 := ((44913990982142858609 : Rat) / 640000000000000000000), D4 := ((11044074089285681651 : Rat) / 320000000000000000000), LB := ((1942487425381667 : Rat) / 1000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8765226760625000008181 : Rat) / 3200000000000000000000), R := ((43846549253571428613 : Rat) / 16000000000000000000), D0 := ((43846549253571428613 : Rat) / 16000000000000000000), D1 := ((14766947653571428613 : Rat) / 16000000000000000000), D2 := ((2919589253571428613 : Rat) / 16000000000000000000), D3 := ((28581630625000000933 : Rat) / 400000000000000000000), D4 := ((106357650803571102091 : Rat) / 3200000000000000000000), LB := ((24080007069378073 : Rat) / 10000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43846549253571428613 : Rat) / 16000000000000000000), R := ((8773392940803571437019 : Rat) / 3200000000000000000000), D0 := ((8773392940803571437019 : Rat) / 3200000000000000000000), D1 := ((2957472620803571437019 : Rat) / 3200000000000000000000), D2 := ((588000940803571437019 : Rat) / 3200000000000000000000), D3 := ((232736135089285721883 : Rat) / 3200000000000000000000), D4 := ((12784320089285673459 : Rat) / 400000000000000000000), LB := ((15638213773783993 : Rat) / 5000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8773392940803571437019 : Rat) / 3200000000000000000000), R := ((4388738015446428575719 : Rat) / 1600000000000000000000), D0 := ((4388738015446428575719 : Rat) / 1600000000000000000000), D1 := ((1480777855446428575719 : Rat) / 1600000000000000000000), D2 := ((296042015446428575719 : Rat) / 1600000000000000000000), D3 := ((118409612589285718151 : Rat) / 1600000000000000000000), D4 := ((98191470624999673253 : Rat) / 3200000000000000000000), LB := ((2058147831351831 : Rat) / 500000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4388738015446428575719 : Rat) / 1600000000000000000000), R := ((2196410552767857145069 : Rat) / 800000000000000000000), D0 := ((2196410552767857145069 : Rat) / 800000000000000000000), D1 := ((742430472767857145069 : Rat) / 800000000000000000000), D2 := ((150062552767857145069 : Rat) / 800000000000000000000), D3 := ((12249270267857143257 : Rat) / 160000000000000000000), D4 := ((47054190267856979417 : Rat) / 1600000000000000000000), LB := ((8656753629081027 : Rat) / 10000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2196410552767857145069 : Rat) / 800000000000000000000), R := ((4396904195625000004557 : Rat) / 1600000000000000000000), D0 := ((4396904195625000004557 : Rat) / 1600000000000000000000), D1 := ((1488944035625000004557 : Rat) / 1600000000000000000000), D2 := ((304208195625000004557 : Rat) / 1600000000000000000000), D3 := ((126575792767857146989 : Rat) / 1600000000000000000000), D4 := ((21485550089285632499 : Rat) / 800000000000000000000), LB := ((8886950715003561 : Rat) / 2000000000000000000) },
  { w1 := ((4616865644311689 : Rat) / 5000000000000000), w2 := ((23697723134774303 : Rat) / 500000000000000000), w3 := ((917237953025429 : Rat) / 6250000000000000), w4 := ((1376535112591559 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133447762589285714299 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4396904195625000004557 : Rat) / 1600000000000000000000), R := ((68765426339285714359 : Rat) / 25000000000000000000), D0 := ((68765426339285714359 : Rat) / 25000000000000000000), D1 := ((23328548839285714359 : Rat) / 25000000000000000000), D2 := ((4817051339285714359 : Rat) / 25000000000000000000), D3 := ((4083090089285714419 : Rat) / 50000000000000000000), D4 := ((38888010089285550579 : Rat) / 1600000000000000000000), LB := ((4719443777135901 : Rat) / 500000000000000000) }
]

def block342RightChunk000L : Rat := ((87521078125000000147 : Rat) / 50000000000000000000)
def block342RightChunk000R : Rat := ((68765426339285714359 : Rat) / 25000000000000000000)

def block342RightChunk000Certificate : Bool :=
  allBoxesValid block342RightChunk000 &&
  coversFromBool block342RightChunk000 block342RightChunk000L block342RightChunk000R

theorem block342RightChunk000Certificate_eq_true :
    block342RightChunk000Certificate = true := by
  native_decide

def block342RightChainCertificate : Bool :=
  decide (
    block342RightL = ((87521078125000000147 : Rat) / 50000000000000000000) /\
    ((68765426339285714359 : Rat) / 25000000000000000000) = block342RightR)

theorem block342RightChainCertificate_eq_true :
    block342RightChainCertificate = true := by
  native_decide

def block342LeftBoxCount : Nat := boxCount block342LeftBoxes
def block342RightBoxCount : Nat := 61

def block342_rational_certificate : Prop :=
    block342LeftCertificate = true /\
    block342RightChainCertificate = true /\
    block342RightChunk000Certificate = true

theorem block342_rational_certificate_proof :
    block342_rational_certificate := by
  exact ⟨block342LeftCertificate_eq_true, block342RightChainCertificate_eq_true, block342RightChunk000Certificate_eq_true⟩

end Block342
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block342

open Set

def block342W1 : Rat := ((4616865644311689 : Rat) / 5000000000000000)
def block342W2 : Rat := ((23697723134774303 : Rat) / 500000000000000000)
def block342W3 : Rat := ((917237953025429 : Rat) / 6250000000000000)
def block342W4 : Rat := ((1376535112591559 : Rat) / 10000000000000000)
def block342S1 : Rat := ((18174751 : Rat) / 10000000)
def block342S2 : Rat := ((511587 : Rat) / 200000)
def block342S3 : Rat := ((133447762589285714299 : Rat) / 50000000000000000000)
def block342S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block342V (y : ℝ) : ℝ :=
  ratPotential block342W1 block342W2 block342W3 block342W4 block342S1 block342S2 block342S3 block342S4 y

def block342LeftParamsCertificate : Bool :=
  allBoxesSameParams block342LeftBoxes block342W1 block342W2 block342W3 block342W4 block342S1 block342S2 block342S3 block342S4

theorem block342LeftParamsCertificate_eq_true :
    block342LeftParamsCertificate = true := by
  native_decide

theorem block342_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block342LeftL : ℝ) (block342LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block342S1 : ℝ))
    (hy2ne : y ≠ (block342S2 : ℝ))
    (hy3ne : y ≠ (block342S3 : ℝ))
    (hy4ne : y ≠ (block342S4 : ℝ)) :
    0 < block342V y := by
  have hcert := block342LeftCertificate_eq_true
  unfold block342LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block342LeftBoxes) (lo := block342LeftL) (hi := block342LeftR)
    (w1 := block342W1) (w2 := block342W2) (w3 := block342W3) (w4 := block342W4)
    (s1 := block342S1) (s2 := block342S2) (s3 := block342S3) (s4 := block342S4)
    hboxes hcover block342LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block342RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block342RightChunk000 block342W1 block342W2 block342W3 block342W4 block342S1 block342S2 block342S3 block342S4

theorem block342RightChunk000ParamsCertificate_eq_true :
    block342RightChunk000ParamsCertificate = true := by
  native_decide

theorem block342_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block342RightChunk000L : ℝ) (block342RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block342S1 : ℝ))
    (hy2ne : y ≠ (block342S2 : ℝ))
    (hy3ne : y ≠ (block342S3 : ℝ))
    (hy4ne : y ≠ (block342S4 : ℝ)) :
    0 < block342V y := by
  have hcert := block342RightChunk000Certificate_eq_true
  unfold block342RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block342RightChunk000) (lo := block342RightChunk000L) (hi := block342RightChunk000R)
    (w1 := block342W1) (w2 := block342W2) (w3 := block342W3) (w4 := block342W4)
    (s1 := block342S1) (s2 := block342S2) (s3 := block342S3) (s4 := block342S4)
    hboxes hcover block342RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block342_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block342RightL : ℝ) (block342RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block342S1 : ℝ))
    (hy2ne : y ≠ (block342S2 : ℝ))
    (hy3ne : y ≠ (block342S3 : ℝ))
    (hy4ne : y ≠ (block342S4 : ℝ)) :
    0 < block342V y := by
  have hL : (block342RightChunk000L : ℝ) = (block342RightL : ℝ) := by
    norm_num [block342RightChunk000L, block342RightL]
  have hR : (block342RightChunk000R : ℝ) = (block342RightR : ℝ) := by
    norm_num [block342RightChunk000R, block342RightR]
  have hyc : y ∈ Icc (block342RightChunk000L : ℝ) (block342RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block342_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block342_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block342LeftL : ℝ) (block342LeftR : ℝ) →
    y ≠ 0 → y ≠ (block342S1 : ℝ) → y ≠ (block342S2 : ℝ) →
    y ≠ (block342S3 : ℝ) → y ≠ (block342S4 : ℝ) → 0 < block342V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block342RightL : ℝ) (block342RightR : ℝ) →
    y ≠ 0 → y ≠ (block342S1 : ℝ) → y ≠ (block342S2 : ℝ) →
    y ≠ (block342S3 : ℝ) → y ≠ (block342S4 : ℝ) → 0 < block342V y)

theorem block342_reallog_certificate_proof :
    block342_reallog_certificate := by
  exact ⟨block342_left_V_pos, block342_right_V_pos⟩

end Block342
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block342.block342V
#check Erdos1038Lean.M1817475.Block342.block342_left_V_pos
#check Erdos1038Lean.M1817475.Block342.block342_right_V_pos
#check Erdos1038Lean.M1817475.Block342.block342_reallog_certificate_proof
