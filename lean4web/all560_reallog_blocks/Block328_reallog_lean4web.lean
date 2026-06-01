/-
Self-contained Lean4Web paste file.
Block 328 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block328

def block328LeftL : Rat := ((37657921875000000141 : Rat) / 50000000000000000000)
def block328LeftR : Rat := ((4708462053571428589 : Rat) / 6250000000000000000)
def block328RightL : Rat := ((87657921875000000141 : Rat) / 50000000000000000000)
def block328RightR : Rat := ((17208462053571428589 : Rat) / 6250000000000000000)

def block328LeftBoxes : List RatBox := [
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37657921875000000141 : Rat) / 50000000000000000000), R := ((4708462053571428589 : Rat) / 6250000000000000000), D0 := ((4708462053571428589 : Rat) / 6250000000000000000), D1 := ((53215833124999999859 : Rat) / 50000000000000000000), D2 := ((90238828124999999859 : Rat) / 50000000000000000000), D3 := ((96092851874999999859 : Rat) / 50000000000000000000), D4 := ((100960584553571423457 : Rat) / 50000000000000000000), LB := ((6703605049318689 : Rat) / 1000000000000000000) }
]

def block328LeftCertificate : Bool :=
  allBoxesValid block328LeftBoxes &&
  coversFromBool block328LeftBoxes block328LeftL block328LeftR

theorem block328LeftCertificate_eq_true :
    block328LeftCertificate = true := by
  native_decide

def block328RightChunk000 : List RatBox := [
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87657921875000000141 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3215833124999999859 : Rat) / 50000000000000000000), D2 := ((40238828124999999859 : Rat) / 50000000000000000000), D3 := ((46092851874999999859 : Rat) / 50000000000000000000), D4 := ((50960584553571423457 : Rat) / 50000000000000000000), LB := ((20439956234106997 : Rat) / 10000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((836516215445689 : Rat) / 4000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((19492417 : Rat) / 40000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((13479208327030193 : Rat) / 100000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((6316047 : Rat) / 16000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((4539829642461437 : Rat) / 50000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((55755871 : Rat) / 160000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((11137805454909 : Rat) / 400000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((6043909 : Rat) / 20000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((249749453215109 : Rat) / 10000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((17859589 : Rat) / 64000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((3711381768502109 : Rat) / 1000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((40946673 : Rat) / 160000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((4521906569246531 : Rat) / 500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((156382093 : Rat) / 640000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((4244650908733147 : Rat) / 2500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((74488747 : Rat) / 320000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((3329985618964179 : Rat) / 500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((290550389 : Rat) / 1280000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((400521899461187 : Rat) / 100000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((28314579 : Rat) / 128000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((8513723849915139 : Rat) / 5000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((275741191 : Rat) / 1280000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((6527816947018393 : Rat) / 1250000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((544077783 : Rat) / 2560000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((4383617680042473 : Rat) / 1000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((16771037 : Rat) / 80000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((36473259275671133 : Rat) / 10000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((105853717 : Rat) / 512000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((15084685057196179 : Rat) / 5000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((260931993 : Rat) / 1280000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((3120402709609997 : Rat) / 1250000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((514459387 : Rat) / 2560000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((522426037665509 : Rat) / 250000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((126763697 : Rat) / 640000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((4504257162905173 : Rat) / 2500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((499650189 : Rat) / 2560000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((8186945338876789 : Rat) / 5000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((49224559 : Rat) / 256000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((500733732582909 : Rat) / 312500000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((484840991 : Rat) / 2560000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((425688716020077 : Rat) / 250000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((59679549 : Rat) / 320000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((4863665671198461 : Rat) / 2500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((470031793 : Rat) / 2560000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((9133318466019 : Rat) / 3906250000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((231313597 : Rat) / 1280000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((288931679023377 : Rat) / 100000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((91044519 : Rat) / 512000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((3608689492575007 : Rat) / 1000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((6407626219 : Rat) / 2560000000), D0 := ((6407626219 : Rat) / 2560000000), D1 := ((1754889963 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((111954499 : Rat) / 640000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((4507202447645103 : Rat) / 1000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6407626219 : Rat) / 2560000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((140687381 : Rat) / 2560000000), D3 := ((440413397 : Rat) / 2560000000), D4 := ((6734778419363836799 : Rat) / 25000000000000000000), LB := ((2798679831607309 : Rat) / 500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((216504399 : Rat) / 1280000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((1094529061180273 : Rat) / 625000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1045499 : Rat) / 6400000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((5066862106456543 : Rat) / 1000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((201695201 : Rat) / 1280000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((2361838614042211 : Rat) / 250000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((97145301 : Rat) / 640000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((10234064514301977 : Rat) / 2000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((44870351 : Rat) / 320000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((85519174987299 : Rat) / 31250000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((823222419 : Rat) / 320000000), D0 := ((823222419 : Rat) / 320000000), D1 := ((241630387 : Rat) / 320000000), D2 := ((4683219 : Rat) / 320000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((19879076725322603 : Rat) / 500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((823222419 : Rat) / 320000000), R := ((413952819 : Rat) / 160000000), D0 := ((413952819 : Rat) / 160000000), D1 := ((123156803 : Rat) / 160000000), D2 := ((4683219 : Rat) / 160000000), D3 := ((32782533 : Rat) / 320000000), D4 := ((4995001729910711799 : Rat) / 25000000000000000000), LB := ((5726189042240773 : Rat) / 500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((413952819 : Rat) / 160000000), R := ((832588857 : Rat) / 320000000), D0 := ((832588857 : Rat) / 320000000), D1 := ((10039873 : Rat) / 12800000), D2 := ((14049657 : Rat) / 320000000), D3 := ((14049657 : Rat) / 160000000), D4 := ((4629125245535711799 : Rat) / 25000000000000000000), LB := ((8659524009362041 : Rat) / 10000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((832588857 : Rat) / 320000000), R := ((209318019 : Rat) / 80000000), D0 := ((209318019 : Rat) / 80000000), D1 := ((63920011 : Rat) / 80000000), D2 := ((4683219 : Rat) / 80000000), D3 := ((4683219 : Rat) / 64000000), D4 := ((4263248761160711799 : Rat) / 25000000000000000000), LB := ((5536999349252253 : Rat) / 5000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((209318019 : Rat) / 80000000), R := ((168391059 : Rat) / 64000000), D0 := ((168391059 : Rat) / 64000000), D1 := ((260363263 : Rat) / 320000000), D2 := ((4683219 : Rat) / 64000000), D3 := ((4683219 : Rat) / 80000000), D4 := ((3897372276785711799 : Rat) / 25000000000000000000), LB := ((2897057734282421 : Rat) / 250000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((168391059 : Rat) / 64000000), R := ((423319257 : Rat) / 160000000), D0 := ((423319257 : Rat) / 160000000), D1 := ((132523241 : Rat) / 160000000), D2 := ((14049657 : Rat) / 160000000), D3 := ((14049657 : Rat) / 320000000), D4 := ((3531495792410711799 : Rat) / 25000000000000000000), LB := ((3474479489192739 : Rat) / 100000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((423319257 : Rat) / 160000000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 160000000), D4 := ((3165619308035711799 : Rat) / 25000000000000000000), LB := ((9905359517559087 : Rat) / 200000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((107000619 : Rat) / 40000000), R := ((67365002209821428589 : Rat) / 25000000000000000000), D0 := ((67365002209821428589 : Rat) / 25000000000000000000), D1 := ((21928124709821428589 : Rat) / 25000000000000000000), D2 := ((3416627209821428589 : Rat) / 25000000000000000000), D3 := ((489615334821428589 : Rat) / 25000000000000000000), D4 := ((2433866339285711799 : Rat) / 25000000000000000000), LB := ((5318659474929993 : Rat) / 50000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((67365002209821428589 : Rat) / 25000000000000000000), R := ((33927308772321428589 : Rat) / 12500000000000000000), D0 := ((33927308772321428589 : Rat) / 12500000000000000000), D1 := ((11208870022321428589 : Rat) / 12500000000000000000), D2 := ((1953121272321428589 : Rat) / 12500000000000000000), D3 := ((489615334821428589 : Rat) / 12500000000000000000), D4 := ((194425100446428321 : Rat) / 2500000000000000000), LB := ((7277700994753 : Rat) / 2000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((33927308772321428589 : Rat) / 12500000000000000000), R := ((271908085513392857301 : Rat) / 100000000000000000000), D0 := ((271908085513392857301 : Rat) / 100000000000000000000), D1 := ((90160575513392857301 : Rat) / 100000000000000000000), D2 := ((16114585513392857301 : Rat) / 100000000000000000000), D3 := ((4406538013392857301 : Rat) / 100000000000000000000), D4 := ((1454635669642854621 : Rat) / 25000000000000000000), LB := ((1798790419684887 : Rat) / 100000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((271908085513392857301 : Rat) / 100000000000000000000), R := ((27239770084821428589 : Rat) / 10000000000000000000), D0 := ((27239770084821428589 : Rat) / 10000000000000000000), D1 := ((9065019084821428589 : Rat) / 10000000000000000000), D2 := ((1660420084821428589 : Rat) / 10000000000000000000), D3 := ((489615334821428589 : Rat) / 10000000000000000000), D4 := ((1065785468749997979 : Rat) / 20000000000000000000), LB := ((823322882845659 : Rat) / 125000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((27239770084821428589 : Rat) / 10000000000000000000), R := ((545285017031250000369 : Rat) / 200000000000000000000), D0 := ((545285017031250000369 : Rat) / 200000000000000000000), D1 := ((181789997031250000369 : Rat) / 200000000000000000000), D2 := ((33698017031250000369 : Rat) / 200000000000000000000), D3 := ((10281922031250000369 : Rat) / 200000000000000000000), D4 := ((2419656004464280653 : Rat) / 50000000000000000000), LB := ((33675881166359 : Rat) / 3906250000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545285017031250000369 : Rat) / 200000000000000000000), R := ((272887316183035714479 : Rat) / 100000000000000000000), D0 := ((272887316183035714479 : Rat) / 100000000000000000000), D1 := ((91139806183035714479 : Rat) / 100000000000000000000), D2 := ((17093816183035714479 : Rat) / 100000000000000000000), D3 := ((5385768683035714479 : Rat) / 100000000000000000000), D4 := ((9189008683035694023 : Rat) / 200000000000000000000), LB := ((4928843881355449 : Rat) / 1000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272887316183035714479 : Rat) / 100000000000000000000), R := ((546264247700892857547 : Rat) / 200000000000000000000), D0 := ((546264247700892857547 : Rat) / 200000000000000000000), D1 := ((182769227700892857547 : Rat) / 200000000000000000000), D2 := ((34677247700892857547 : Rat) / 200000000000000000000), D3 := ((11261152700892857547 : Rat) / 200000000000000000000), D4 := ((4349696674107132717 : Rat) / 100000000000000000000), LB := ((3872983224086357 : Rat) / 2000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546264247700892857547 : Rat) / 200000000000000000000), R := ((1093018110736607143683 : Rat) / 400000000000000000000), D0 := ((1093018110736607143683 : Rat) / 400000000000000000000), D1 := ((366028070736607143683 : Rat) / 400000000000000000000), D2 := ((69844110736607143683 : Rat) / 400000000000000000000), D3 := ((23011920736607143683 : Rat) / 400000000000000000000), D4 := ((1641955602678567369 : Rat) / 40000000000000000000), LB := ((9435822855060283 : Rat) / 2000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1093018110736607143683 : Rat) / 400000000000000000000), R := ((68344232879464285767 : Rat) / 25000000000000000000), D0 := ((68344232879464285767 : Rat) / 25000000000000000000), D1 := ((22907355379464285767 : Rat) / 25000000000000000000), D2 := ((4395857879464285767 : Rat) / 25000000000000000000), D3 := ((1468846004464285767 : Rat) / 25000000000000000000), D4 := ((15929940691964245101 : Rat) / 400000000000000000000), LB := ((1897205110462069 : Rat) / 500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((68344232879464285767 : Rat) / 25000000000000000000), R := ((1093997341406250000861 : Rat) / 400000000000000000000), D0 := ((1093997341406250000861 : Rat) / 400000000000000000000), D1 := ((367007301406250000861 : Rat) / 400000000000000000000), D2 := ((70823341406250000861 : Rat) / 400000000000000000000), D3 := ((23991151406250000861 : Rat) / 400000000000000000000), D4 := ((60313770926339127 : Rat) / 1562500000000000000), LB := ((766471022859469 : Rat) / 250000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1093997341406250000861 : Rat) / 400000000000000000000), R := ((21889739134821428589 : Rat) / 8000000000000000000), D0 := ((21889739134821428589 : Rat) / 8000000000000000000), D1 := ((7349938334821428589 : Rat) / 8000000000000000000), D2 := ((1426259134821428589 : Rat) / 8000000000000000000), D3 := ((489615334821428589 : Rat) / 8000000000000000000), D4 := ((14950710022321387923 : Rat) / 400000000000000000000), LB := ((3965800468189 : Rat) / 1562500000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21889739134821428589 : Rat) / 8000000000000000000), R := ((1094976572075892858039 : Rat) / 400000000000000000000), D0 := ((1094976572075892858039 : Rat) / 400000000000000000000), D1 := ((367986532075892858039 : Rat) / 400000000000000000000), D2 := ((71802572075892858039 : Rat) / 400000000000000000000), D3 := ((24970382075892858039 : Rat) / 400000000000000000000), D4 := ((7230547343749979667 : Rat) / 200000000000000000000), LB := ((11089268732605573 : Rat) / 5000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094976572075892858039 : Rat) / 400000000000000000000), R := ((273866546852678571657 : Rat) / 100000000000000000000), D0 := ((273866546852678571657 : Rat) / 100000000000000000000), D1 := ((92119036852678571657 : Rat) / 100000000000000000000), D2 := ((18073046852678571657 : Rat) / 100000000000000000000), D3 := ((6364999352678571657 : Rat) / 100000000000000000000), D4 := ((2794295870535706149 : Rat) / 80000000000000000000), LB := ((1056474953921277 : Rat) / 500000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((273866546852678571657 : Rat) / 100000000000000000000), R := ((1095955802745535715217 : Rat) / 400000000000000000000), D0 := ((1095955802745535715217 : Rat) / 400000000000000000000), D1 := ((368965762745535715217 : Rat) / 400000000000000000000), D2 := ((72781802745535715217 : Rat) / 400000000000000000000), D3 := ((25949612745535715217 : Rat) / 400000000000000000000), D4 := ((3370466004464275539 : Rat) / 100000000000000000000), LB := ((11162246476323079 : Rat) / 5000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1095955802745535715217 : Rat) / 400000000000000000000), R := ((548222709040178571903 : Rat) / 200000000000000000000), D0 := ((548222709040178571903 : Rat) / 200000000000000000000), D1 := ((184727689040178571903 : Rat) / 200000000000000000000), D2 := ((36635709040178571903 : Rat) / 200000000000000000000), D3 := ((13219614040178571903 : Rat) / 200000000000000000000), D4 := ((12992248683035673567 : Rat) / 400000000000000000000), LB := ((25867578576856953 : Rat) / 10000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((548222709040178571903 : Rat) / 200000000000000000000), R := ((219387006683035714479 : Rat) / 80000000000000000000), D0 := ((219387006683035714479 : Rat) / 80000000000000000000), D1 := ((73988998683035714479 : Rat) / 80000000000000000000), D2 := ((14752206683035714479 : Rat) / 80000000000000000000), D3 := ((5385768683035714479 : Rat) / 80000000000000000000), D4 := ((6251316674107122489 : Rat) / 200000000000000000000), LB := ((31878209726644013 : Rat) / 10000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((219387006683035714479 : Rat) / 80000000000000000000), R := ((137178081093750000123 : Rat) / 50000000000000000000), D0 := ((137178081093750000123 : Rat) / 50000000000000000000), D1 := ((46304326093750000123 : Rat) / 50000000000000000000), D2 := ((9281331093750000123 : Rat) / 50000000000000000000), D3 := ((3427307343750000123 : Rat) / 50000000000000000000), D4 := ((12013018013392816389 : Rat) / 400000000000000000000), LB := ((404934430189019 : Rat) / 100000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((137178081093750000123 : Rat) / 50000000000000000000), R := ((549201939709821429081 : Rat) / 200000000000000000000), D0 := ((549201939709821429081 : Rat) / 200000000000000000000), D1 := ((185706919709821429081 : Rat) / 200000000000000000000), D2 := ((37614939709821429081 : Rat) / 200000000000000000000), D3 := ((14198844709821429081 : Rat) / 200000000000000000000), D4 := ((57617013392856939 : Rat) / 2000000000000000000), LB := ((6944943311349427 : Rat) / 10000000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((549201939709821429081 : Rat) / 200000000000000000000), R := ((54969155504464285767 : Rat) / 20000000000000000000), D0 := ((54969155504464285767 : Rat) / 20000000000000000000), D1 := ((18619653504464285767 : Rat) / 20000000000000000000), D2 := ((3810455504464285767 : Rat) / 20000000000000000000), D3 := ((1468846004464285767 : Rat) / 20000000000000000000), D4 := ((5272086004464265311 : Rat) / 200000000000000000000), LB := ((158584000218851 : Rat) / 40000000000000000) },
  { w1 := ((9556106182834753 : Rat) / 10000000000000000), w2 := ((4752889916153827 : Rat) / 100000000000000000), w3 := ((1423557206171207 : Rat) / 10000000000000000), w4 := ((2729097987059903 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((54969155504464285767 : Rat) / 20000000000000000000), R := ((17208462053571428589 : Rat) / 6250000000000000000), D0 := ((17208462053571428589 : Rat) / 6250000000000000000), D1 := ((5849242678571428589 : Rat) / 6250000000000000000), D2 := ((1221368303571428589 : Rat) / 6250000000000000000), D3 := ((489615334821428589 : Rat) / 6250000000000000000), D4 := ((2391235334821418361 : Rat) / 100000000000000000000), LB := ((3946769381324433 : Rat) / 50000000000000000000) }
]

def block328RightChunk000L : Rat := ((87657921875000000141 : Rat) / 50000000000000000000)
def block328RightChunk000R : Rat := ((17208462053571428589 : Rat) / 6250000000000000000)

def block328RightChunk000Certificate : Bool :=
  allBoxesValid block328RightChunk000 &&
  coversFromBool block328RightChunk000 block328RightChunk000L block328RightChunk000R

theorem block328RightChunk000Certificate_eq_true :
    block328RightChunk000Certificate = true := by
  native_decide

def block328RightChainCertificate : Bool :=
  decide (
    block328RightL = ((87657921875000000141 : Rat) / 50000000000000000000) /\
    ((17208462053571428589 : Rat) / 6250000000000000000) = block328RightR)

theorem block328RightChainCertificate_eq_true :
    block328RightChainCertificate = true := by
  native_decide

def block328LeftBoxCount : Nat := boxCount block328LeftBoxes
def block328RightBoxCount : Nat := 60

def block328_rational_certificate : Prop :=
    block328LeftCertificate = true /\
    block328RightChainCertificate = true /\
    block328RightChunk000Certificate = true

theorem block328_rational_certificate_proof :
    block328_rational_certificate := by
  exact ⟨block328LeftCertificate_eq_true, block328RightChainCertificate_eq_true, block328RightChunk000Certificate_eq_true⟩

end Block328
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block328

open Set

def block328W1 : Rat := ((9556106182834753 : Rat) / 10000000000000000)
def block328W2 : Rat := ((4752889916153827 : Rat) / 100000000000000000)
def block328W3 : Rat := ((1423557206171207 : Rat) / 10000000000000000)
def block328W4 : Rat := ((2729097987059903 : Rat) / 20000000000000000)
def block328S1 : Rat := ((18174751 : Rat) / 10000000)
def block328S2 : Rat := ((511587 : Rat) / 200000)
def block328S3 : Rat := ((107000619 : Rat) / 40000000)
def block328S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block328V (y : ℝ) : ℝ :=
  ratPotential block328W1 block328W2 block328W3 block328W4 block328S1 block328S2 block328S3 block328S4 y

def block328LeftParamsCertificate : Bool :=
  allBoxesSameParams block328LeftBoxes block328W1 block328W2 block328W3 block328W4 block328S1 block328S2 block328S3 block328S4

theorem block328LeftParamsCertificate_eq_true :
    block328LeftParamsCertificate = true := by
  native_decide

theorem block328_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block328LeftL : ℝ) (block328LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block328S1 : ℝ))
    (hy2ne : y ≠ (block328S2 : ℝ))
    (hy3ne : y ≠ (block328S3 : ℝ))
    (hy4ne : y ≠ (block328S4 : ℝ)) :
    0 < block328V y := by
  have hcert := block328LeftCertificate_eq_true
  unfold block328LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block328LeftBoxes) (lo := block328LeftL) (hi := block328LeftR)
    (w1 := block328W1) (w2 := block328W2) (w3 := block328W3) (w4 := block328W4)
    (s1 := block328S1) (s2 := block328S2) (s3 := block328S3) (s4 := block328S4)
    hboxes hcover block328LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block328RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block328RightChunk000 block328W1 block328W2 block328W3 block328W4 block328S1 block328S2 block328S3 block328S4

theorem block328RightChunk000ParamsCertificate_eq_true :
    block328RightChunk000ParamsCertificate = true := by
  native_decide

theorem block328_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block328RightChunk000L : ℝ) (block328RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block328S1 : ℝ))
    (hy2ne : y ≠ (block328S2 : ℝ))
    (hy3ne : y ≠ (block328S3 : ℝ))
    (hy4ne : y ≠ (block328S4 : ℝ)) :
    0 < block328V y := by
  have hcert := block328RightChunk000Certificate_eq_true
  unfold block328RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block328RightChunk000) (lo := block328RightChunk000L) (hi := block328RightChunk000R)
    (w1 := block328W1) (w2 := block328W2) (w3 := block328W3) (w4 := block328W4)
    (s1 := block328S1) (s2 := block328S2) (s3 := block328S3) (s4 := block328S4)
    hboxes hcover block328RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block328_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block328RightL : ℝ) (block328RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block328S1 : ℝ))
    (hy2ne : y ≠ (block328S2 : ℝ))
    (hy3ne : y ≠ (block328S3 : ℝ))
    (hy4ne : y ≠ (block328S4 : ℝ)) :
    0 < block328V y := by
  have hL : (block328RightChunk000L : ℝ) = (block328RightL : ℝ) := by
    norm_num [block328RightChunk000L, block328RightL]
  have hR : (block328RightChunk000R : ℝ) = (block328RightR : ℝ) := by
    norm_num [block328RightChunk000R, block328RightR]
  have hyc : y ∈ Icc (block328RightChunk000L : ℝ) (block328RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block328_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block328_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block328LeftL : ℝ) (block328LeftR : ℝ) →
    y ≠ 0 → y ≠ (block328S1 : ℝ) → y ≠ (block328S2 : ℝ) →
    y ≠ (block328S3 : ℝ) → y ≠ (block328S4 : ℝ) → 0 < block328V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block328RightL : ℝ) (block328RightR : ℝ) →
    y ≠ 0 → y ≠ (block328S1 : ℝ) → y ≠ (block328S2 : ℝ) →
    y ≠ (block328S3 : ℝ) → y ≠ (block328S4 : ℝ) → 0 < block328V y)

theorem block328_reallog_certificate_proof :
    block328_reallog_certificate := by
  exact ⟨block328_left_V_pos, block328_right_V_pos⟩

end Block328
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block328.block328V
#check Erdos1038Lean.M1817475.Block328.block328_left_V_pos
#check Erdos1038Lean.M1817475.Block328.block328_right_V_pos
#check Erdos1038Lean.M1817475.Block328.block328_reallog_certificate_proof
