/-
Self-contained Lean4Web paste file.
Block 314 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block314

def block314LeftL : Rat := ((7558953125000000027 : Rat) / 10000000000000000000)
def block314LeftR : Rat := ((18902270089285714353 : Rat) / 25000000000000000000)
def block314RightL : Rat := ((17558953125000000027 : Rat) / 10000000000000000000)
def block314RightR : Rat := ((68902270089285714353 : Rat) / 25000000000000000000)

def block314LeftBoxes : List RatBox := [
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((7558953125000000027 : Rat) / 10000000000000000000), R := ((18902270089285714353 : Rat) / 25000000000000000000), D0 := ((18902270089285714353 : Rat) / 25000000000000000000), D1 := ((10615797874999999973 : Rat) / 10000000000000000000), D2 := ((18020396874999999973 : Rat) / 10000000000000000000), D3 := ((1965060564285714281 : Rat) / 1000000000000000000), D4 := ((102153080089285709119 : Rat) / 50000000000000000000), LB := ((1432658636930137 : Rat) / 125000000000000000) }
]

def block314LeftCertificate : Bool :=
  allBoxesValid block314LeftBoxes &&
  coversFromBool block314LeftBoxes block314LeftL block314LeftR

theorem block314LeftCertificate_eq_true :
    block314LeftCertificate = true := by
  native_decide

def block314RightChunk000 : List RatBox := [
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((17558953125000000027 : Rat) / 10000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((615797874999999973 : Rat) / 10000000000000000000), D2 := ((8020396874999999973 : Rat) / 10000000000000000000), D3 := ((965060564285714281 : Rat) / 1000000000000000000), D4 := ((52153080089285709119 : Rat) / 50000000000000000000), LB := ((2622402453787881 : Rat) / 1250000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((24537045357142854627 : Rat) / 25000000000000000000), LB := ((5365276879278761 : Rat) / 25000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((15281296607142854627 : Rat) / 25000000000000000000), LB := ((431930229099153 : Rat) / 3125000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((4406933392857142837 : Rat) / 10000000000000000000), D4 := ((12967359419642854627 : Rat) / 25000000000000000000), LB := ((9375147942098823 : Rat) / 100000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3944145955357142837 : Rat) / 10000000000000000000), D4 := ((11810390825892854627 : Rat) / 25000000000000000000), LB := ((30546603133047023 : Rat) / 1000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((10653422232142854627 : Rat) / 25000000000000000000), LB := ((2772211971511357 : Rat) / 100000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((3249964799107142837 : Rat) / 10000000000000000000), D4 := ((10074937935267854627 : Rat) / 25000000000000000000), LB := ((25465525180223 : Rat) / 3906250000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((3018571080357142837 : Rat) / 10000000000000000000), D4 := ((9496453638392854627 : Rat) / 25000000000000000000), LB := ((6042071592421677 : Rat) / 500000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2902874220982142837 : Rat) / 10000000000000000000), D4 := ((9207211489955354627 : Rat) / 25000000000000000000), LB := ((39065225536421 : Rat) / 8000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2787177361607142837 : Rat) / 10000000000000000000), D4 := ((8917969341517854627 : Rat) / 25000000000000000000), LB := ((10073259951595581 : Rat) / 1000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2729328931919642837 : Rat) / 10000000000000000000), D4 := ((8773348267299104627 : Rat) / 25000000000000000000), LB := ((18856841802024349 : Rat) / 2500000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2671480502232142837 : Rat) / 10000000000000000000), D4 := ((8628727193080354627 : Rat) / 25000000000000000000), LB := ((1346116995901217 : Rat) / 250000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2613632072544642837 : Rat) / 10000000000000000000), D4 := ((8484106118861604627 : Rat) / 25000000000000000000), LB := ((28294477764923 : Rat) / 7812500000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((8339485044642854627 : Rat) / 25000000000000000000), LB := ((2281599703776893 : Rat) / 1000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((2497935213169642837 : Rat) / 10000000000000000000), D4 := ((8194863970424104627 : Rat) / 25000000000000000000), LB := ((2792550951989603 : Rat) / 2000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((2440086783482142837 : Rat) / 10000000000000000000), D4 := ((8050242896205354627 : Rat) / 25000000000000000000), LB := ((10039834380649593 : Rat) / 10000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((2382238353794642837 : Rat) / 10000000000000000000), D4 := ((7905621821986604627 : Rat) / 25000000000000000000), LB := ((2877253581051037 : Rat) / 2500000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((2324389924107142837 : Rat) / 10000000000000000000), D4 := ((7761000747767854627 : Rat) / 25000000000000000000), LB := ((18935493767284761 : Rat) / 10000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((2266541494419642837 : Rat) / 10000000000000000000), D4 := ((7616379673549104627 : Rat) / 25000000000000000000), LB := ((6604524088770769 : Rat) / 2000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((2208693064732142837 : Rat) / 10000000000000000000), D4 := ((7471758599330354627 : Rat) / 25000000000000000000), LB := ((5466305069291799 : Rat) / 1000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((2150844635044642837 : Rat) / 10000000000000000000), D4 := ((7327137525111604627 : Rat) / 25000000000000000000), LB := ((4250837085630871 : Rat) / 500000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((7182516450892854627 : Rat) / 25000000000000000000), LB := ((95075330511043 : Rat) / 40000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1977299345982142837 : Rat) / 10000000000000000000), D4 := ((6893274302455354627 : Rat) / 25000000000000000000), LB := ((733701824996727 : Rat) / 50000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((6604032154017854627 : Rat) / 25000000000000000000), LB := ((394327224231153 : Rat) / 25000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((6025547857142854627 : Rat) / 25000000000000000000), LB := ((4787670744998751 : Rat) / 200000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((88257721874999959847 : Rat) / 400000000000000000000), LB := ((16665720721853683 : Rat) / 1000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((168364399910714205509 : Rat) / 800000000000000000000), LB := ((15094919563558573 : Rat) / 10000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((40053339017857122831 : Rat) / 200000000000000000000), LB := ((6710062984984777 : Rat) / 1000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((312275668303571268463 : Rat) / 1600000000000000000000), LB := ((30429580834726577 : Rat) / 10000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((152062312232142777139 : Rat) / 800000000000000000000), LB := ((1322744405717613 : Rat) / 2500000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((295973580624999840093 : Rat) / 1600000000000000000000), LB := ((5759873913633307 : Rat) / 1000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((583796117410713966001 : Rat) / 3200000000000000000000), LB := ((666002070235483 : Rat) / 125000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((71955634196428531477 : Rat) / 400000000000000000000), LB := ((161494751809807 : Rat) / 31250000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((567494029732142537631 : Rat) / 3200000000000000000000), LB := ((5278613718129321 : Rat) / 1000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((279671492946428411723 : Rat) / 1600000000000000000000), LB := ((1415304059458583 : Rat) / 250000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((551191942053571109261 : Rat) / 3200000000000000000000), LB := ((157949537660651 : Rat) / 25000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((135760224553571348769 : Rat) / 800000000000000000000), LB := ((2391790461688359 : Rat) / 2000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((263369405267856983353 : Rat) / 1600000000000000000000), LB := ((254688811594371 : Rat) / 62500000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((15951147589285704323 : Rat) / 100000000000000000000), LB := ((406583259492399 : Rat) / 50000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((247067317589285554983 : Rat) / 1600000000000000000000), LB := ((3363326108846959 : Rat) / 250000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((119458136874999920399 : Rat) / 800000000000000000000), LB := ((4626346820388483 : Rat) / 500000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((55653546517857103107 : Rat) / 400000000000000000000), LB := ((7242265034740569 : Rat) / 1000000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((23751251339285694461 : Rat) / 200000000000000000000), LB := ((8705438535502541 : Rat) / 250000000000000000) },
  { w1 := ((1198488392300747 : Rat) / 1250000000000000), w2 := ((3089862464016827 : Rat) / 50000000000000000), w3 := ((12911725786245337 : Rat) / 50000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69973922857142854627 : Rat) / 25000000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((68902270089285714353 : Rat) / 25000000000000000000), D0 := ((68902270089285714353 : Rat) / 25000000000000000000), D1 := ((23465392589285714353 : Rat) / 25000000000000000000), D2 := ((4953895089285714353 : Rat) / 25000000000000000000), D3 := ((1756746339285714521 : Rat) / 50000000000000000000), D4 := ((3900051874999995069 : Rat) / 50000000000000000000), LB := ((11670243373880007 : Rat) / 1000000000000000000) }
]

def block314RightChunk000L : Rat := ((17558953125000000027 : Rat) / 10000000000000000000)
def block314RightChunk000R : Rat := ((68902270089285714353 : Rat) / 25000000000000000000)

def block314RightChunk000Certificate : Bool :=
  allBoxesValid block314RightChunk000 &&
  coversFromBool block314RightChunk000 block314RightChunk000L block314RightChunk000R

theorem block314RightChunk000Certificate_eq_true :
    block314RightChunk000Certificate = true := by
  native_decide

def block314RightChainCertificate : Bool :=
  decide (
    block314RightL = ((17558953125000000027 : Rat) / 10000000000000000000) /\
    ((68902270089285714353 : Rat) / 25000000000000000000) = block314RightR)

theorem block314RightChainCertificate_eq_true :
    block314RightChainCertificate = true := by
  native_decide

def block314LeftBoxCount : Nat := boxCount block314LeftBoxes
def block314RightBoxCount : Nat := 44

def block314_rational_certificate : Prop :=
    block314LeftCertificate = true /\
    block314RightChainCertificate = true /\
    block314RightChunk000Certificate = true

theorem block314_rational_certificate_proof :
    block314_rational_certificate := by
  exact ⟨block314LeftCertificate_eq_true, block314RightChainCertificate_eq_true, block314RightChunk000Certificate_eq_true⟩

end Block314
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block314

open Set

def block314W1 : Rat := ((1198488392300747 : Rat) / 1250000000000000)
def block314W2 : Rat := ((3089862464016827 : Rat) / 50000000000000000)
def block314W3 : Rat := ((12911725786245337 : Rat) / 50000000000000000)
def block314W4 : Rat := (0 : Rat)
def block314S1 : Rat := ((18174751 : Rat) / 10000000)
def block314S2 : Rat := ((511587 : Rat) / 200000)
def block314S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block314S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block314V (y : ℝ) : ℝ :=
  ratPotential block314W1 block314W2 block314W3 block314W4 block314S1 block314S2 block314S3 block314S4 y

def block314LeftParamsCertificate : Bool :=
  allBoxesSameParams block314LeftBoxes block314W1 block314W2 block314W3 block314W4 block314S1 block314S2 block314S3 block314S4

theorem block314LeftParamsCertificate_eq_true :
    block314LeftParamsCertificate = true := by
  native_decide

theorem block314_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block314LeftL : ℝ) (block314LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block314S1 : ℝ))
    (hy2ne : y ≠ (block314S2 : ℝ))
    (hy3ne : y ≠ (block314S3 : ℝ))
    (hy4ne : y ≠ (block314S4 : ℝ)) :
    0 < block314V y := by
  have hcert := block314LeftCertificate_eq_true
  unfold block314LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block314LeftBoxes) (lo := block314LeftL) (hi := block314LeftR)
    (w1 := block314W1) (w2 := block314W2) (w3 := block314W3) (w4 := block314W4)
    (s1 := block314S1) (s2 := block314S2) (s3 := block314S3) (s4 := block314S4)
    hboxes hcover block314LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block314RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block314RightChunk000 block314W1 block314W2 block314W3 block314W4 block314S1 block314S2 block314S3 block314S4

theorem block314RightChunk000ParamsCertificate_eq_true :
    block314RightChunk000ParamsCertificate = true := by
  native_decide

theorem block314_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block314RightChunk000L : ℝ) (block314RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block314S1 : ℝ))
    (hy2ne : y ≠ (block314S2 : ℝ))
    (hy3ne : y ≠ (block314S3 : ℝ))
    (hy4ne : y ≠ (block314S4 : ℝ)) :
    0 < block314V y := by
  have hcert := block314RightChunk000Certificate_eq_true
  unfold block314RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block314RightChunk000) (lo := block314RightChunk000L) (hi := block314RightChunk000R)
    (w1 := block314W1) (w2 := block314W2) (w3 := block314W3) (w4 := block314W4)
    (s1 := block314S1) (s2 := block314S2) (s3 := block314S3) (s4 := block314S4)
    hboxes hcover block314RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block314_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block314RightL : ℝ) (block314RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block314S1 : ℝ))
    (hy2ne : y ≠ (block314S2 : ℝ))
    (hy3ne : y ≠ (block314S3 : ℝ))
    (hy4ne : y ≠ (block314S4 : ℝ)) :
    0 < block314V y := by
  have hL : (block314RightChunk000L : ℝ) = (block314RightL : ℝ) := by
    norm_num [block314RightChunk000L, block314RightL]
  have hR : (block314RightChunk000R : ℝ) = (block314RightR : ℝ) := by
    norm_num [block314RightChunk000R, block314RightR]
  have hyc : y ∈ Icc (block314RightChunk000L : ℝ) (block314RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block314_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block314_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block314LeftL : ℝ) (block314LeftR : ℝ) →
    y ≠ 0 → y ≠ (block314S1 : ℝ) → y ≠ (block314S2 : ℝ) →
    y ≠ (block314S3 : ℝ) → y ≠ (block314S4 : ℝ) → 0 < block314V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block314RightL : ℝ) (block314RightR : ℝ) →
    y ≠ 0 → y ≠ (block314S1 : ℝ) → y ≠ (block314S2 : ℝ) →
    y ≠ (block314S3 : ℝ) → y ≠ (block314S4 : ℝ) → 0 < block314V y)

theorem block314_reallog_certificate_proof :
    block314_reallog_certificate := by
  exact ⟨block314_left_V_pos, block314_right_V_pos⟩

end Block314
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block314.block314V
#check Erdos1038Lean.M1817475.Block314.block314_left_V_pos
#check Erdos1038Lean.M1817475.Block314.block314_right_V_pos
#check Erdos1038Lean.M1817475.Block314.block314_reallog_certificate_proof
