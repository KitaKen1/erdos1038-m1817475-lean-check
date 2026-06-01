/-
Self-contained Lean4Web paste file.
Block 181 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block181

def block181LeftL : Rat := ((19547390625000000039 : Rat) / 25000000000000000000)
def block181LeftR : Rat := ((39104555803571428649 : Rat) / 50000000000000000000)
def block181RightL : Rat := ((44547390625000000039 : Rat) / 25000000000000000000)
def block181RightR : Rat := ((139104555803571428649 : Rat) / 50000000000000000000)

def block181LeftBoxes : List RatBox := [
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((19547390625000000039 : Rat) / 25000000000000000000), R := ((39104555803571428649 : Rat) / 50000000000000000000), D0 := ((39104555803571428649 : Rat) / 50000000000000000000), D1 := ((25889486874999999961 : Rat) / 25000000000000000000), D2 := ((44400984374999999961 : Rat) / 25000000000000000000), D3 := ((96953012589285714107 : Rat) / 50000000000000000000), D4 := ((50064873749999997461 : Rat) / 25000000000000000000), LB := ((10095745455594163 : Rat) / 10000000000000000000) }
]

def block181LeftCertificate : Bool :=
  allBoxesValid block181LeftBoxes &&
  coversFromBool block181LeftBoxes block181LeftL block181LeftR

theorem block181LeftCertificate_eq_true :
    block181LeftCertificate = true := by
  native_decide

def block181RightChunk000 : List RatBox := [
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((44547390625000000039 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((889486874999999961 : Rat) / 25000000000000000000), D2 := ((19400984374999999961 : Rat) / 25000000000000000000), D3 := ((46953012589285714107 : Rat) / 50000000000000000000), D4 := ((25064873749999997461 : Rat) / 25000000000000000000), LB := ((5363375941214047 : Rat) / 1000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((10103237565414733 : Rat) / 10000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((17218056359217643 : Rat) / 50000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((353216760523517 : Rat) / 2500000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((7806446451747467 : Rat) / 100000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((1508446344423147 : Rat) / 25000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((235901722773649 : Rat) / 10000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((410899808767857142837 : Rat) / 160000000000000000000), D0 := ((410899808767857142837 : Rat) / 160000000000000000000), D1 := ((120103792767857142837 : Rat) / 160000000000000000000), D2 := ((1630208767857142837 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((5550355533262069 : Rat) / 200000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((410899808767857142837 : Rat) / 160000000000000000000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 32000000000000000000), D4 := ((34618683232142841163 : Rat) / 160000000000000000000), LB := ((15431446684209149 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((4436927592536749 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((4264056942354641 : Rat) / 500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((61086322624999968141 : Rat) / 320000000000000000000), LB := ((854394540543979 : Rat) / 200000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((4432587066195981 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((9488425437556361 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((114021601410714222097 : Rat) / 640000000000000000000), LB := ((22680909653263193 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((8660271324988367 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((3344255777017857141991 : Rat) / 1280000000000000000000), D0 := ((3344255777017857141991 : Rat) / 1280000000000000000000), D1 := ((1017887649017857141991 : Rat) / 1280000000000000000000), D2 := ((70098977017857141991 : Rat) / 1280000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((14676120935408349 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3344255777017857141991 : Rat) / 1280000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((27713549053571428229 : Rat) / 256000000000000000000), D4 := ((219892158982142730009 : Rat) / 1280000000000000000000), LB := ((2344281568047807 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((669503238910714285533 : Rat) / 256000000000000000000), D0 := ((669503238910714285533 : Rat) / 256000000000000000000), D1 := ((204229613310714285533 : Rat) / 256000000000000000000), D2 := ((14671878910714285533 : Rat) / 256000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((17875560328589613 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((669503238910714285533 : Rat) / 256000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((135307327732142855471 : Rat) / 1280000000000000000000), D4 := ((43326348289285688867 : Rat) / 256000000000000000000), LB := ((2531379851296589 : Rat) / 2000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((779348466225821 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((32922083539604907 : Rat) / 100000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((6706443850482142855189 : Rat) / 2560000000000000000000), D0 := ((6706443850482142855189 : Rat) / 2560000000000000000000), D1 := ((2053707594482142855189 : Rat) / 2560000000000000000000), D2 := ((158130250482142855189 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((196790650591111 : Rat) / 125000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6706443850482142855189 : Rat) / 2560000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((259203194089285711083 : Rat) / 2560000000000000000000), D4 := ((421852021517856888811 : Rat) / 2560000000000000000000), LB := ((690311372100183 : Rat) / 500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((6709704268017857140863 : Rat) / 2560000000000000000000), D0 := ((6709704268017857140863 : Rat) / 2560000000000000000000), D1 := ((2056968012017857140863 : Rat) / 2560000000000000000000), D2 := ((161390668017857140863 : Rat) / 2560000000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((11964339836260107 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6709704268017857140863 : Rat) / 2560000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((255942776553571425409 : Rat) / 2560000000000000000000), D4 := ((418591603982142603137 : Rat) / 2560000000000000000000), LB := ((5109279126123273 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((6712964685553571426537 : Rat) / 2560000000000000000000), D0 := ((6712964685553571426537 : Rat) / 2560000000000000000000), D1 := ((2060228429553571426537 : Rat) / 2560000000000000000000), D2 := ((164651085553571426537 : Rat) / 2560000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((2142467459967587 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6712964685553571426537 : Rat) / 2560000000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((50536471803571427947 : Rat) / 512000000000000000000), D4 := ((415331186446428317463 : Rat) / 2560000000000000000000), LB := ((7019280328628141 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((6716225103089285712211 : Rat) / 2560000000000000000000), D0 := ((6716225103089285712211 : Rat) / 2560000000000000000000), D1 := ((2063488847089285712211 : Rat) / 2560000000000000000000), D2 := ((167911503089285712211 : Rat) / 2560000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((5567814493908363 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6716225103089285712211 : Rat) / 2560000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((249421941482142854061 : Rat) / 2560000000000000000000), D4 := ((412070768910714031789 : Rat) / 2560000000000000000000), LB := ((52706457976677 : Rat) / 125000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((1343897104124999999577 : Rat) / 512000000000000000000), D0 := ((1343897104124999999577 : Rat) / 512000000000000000000), D1 := ((413349852924999999577 : Rat) / 512000000000000000000), D2 := ((34234384124999999577 : Rat) / 512000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((5932902174961563 : Rat) / 20000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1343897104124999999577 : Rat) / 512000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((246161523946428568387 : Rat) / 2560000000000000000000), D4 := ((81762070274999949223 : Rat) / 512000000000000000000), LB := ((18187027046720483 : Rat) / 100000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((7743774185206553 : Rat) / 100000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((2689424417017857141991 : Rat) / 1024000000000000000000), D0 := ((2689424417017857141991 : Rat) / 1024000000000000000000), D1 := ((828329914617857141991 : Rat) / 1024000000000000000000), D2 := ((70098977017857141991 : Rat) / 1024000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((405549933839285460441 : Rat) / 2560000000000000000000), LB := ((4033007104058961 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2689424417017857141991 : Rat) / 1024000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((484172004053571422589 : Rat) / 5120000000000000000000), D4 := ((161893931782142755609 : Rat) / 1024000000000000000000), LB := ((7632783634147489 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((13450382502624999995629 : Rat) / 5120000000000000000000), D0 := ((13450382502624999995629 : Rat) / 5120000000000000000000), D1 := ((4144909990624999995629 : Rat) / 5120000000000000000000), D2 := ((353755302624999995629 : Rat) / 5120000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((7226125836321817 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13450382502624999995629 : Rat) / 5120000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((96182317303571427383 : Rat) / 1024000000000000000000), D4 := ((806209241374999492371 : Rat) / 5120000000000000000000), LB := ((106971688878057 : Rat) / 156250000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((13453642920160714281303 : Rat) / 5120000000000000000000), D0 := ((13453642920160714281303 : Rat) / 5120000000000000000000), D1 := ((4148170408160714281303 : Rat) / 5120000000000000000000), D2 := ((357015720160714281303 : Rat) / 5120000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((6493119123514857 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13453642920160714281303 : Rat) / 5120000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((477651168982142851241 : Rat) / 5120000000000000000000), D4 := ((802948823839285206697 : Rat) / 5120000000000000000000), LB := ((1541767288887469 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((13456903337696428566977 : Rat) / 5120000000000000000000), D0 := ((13456903337696428566977 : Rat) / 5120000000000000000000), D1 := ((4151430825696428566977 : Rat) / 5120000000000000000000), D2 := ((360276137696428566977 : Rat) / 5120000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((2934094948374849 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13456903337696428566977 : Rat) / 5120000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((474390751446428565567 : Rat) / 5120000000000000000000), D4 := ((799688406303570921023 : Rat) / 5120000000000000000000), LB := ((2798317289359753 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((13460163755232142852651 : Rat) / 5120000000000000000000), D0 := ((13460163755232142852651 : Rat) / 5120000000000000000000), D1 := ((4154691243232142852651 : Rat) / 5120000000000000000000), D2 := ((363536555232142852651 : Rat) / 5120000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((214102318902909 : Rat) / 400000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13460163755232142852651 : Rat) / 5120000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((471130333910714279893 : Rat) / 5120000000000000000000), D4 := ((796427988767856635349 : Rat) / 5120000000000000000000), LB := ((2568058204793361 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((538536966910714285533 : Rat) / 204800000000000000000), D0 := ((538536966910714285533 : Rat) / 204800000000000000000), D1 := ((166318066430714285533 : Rat) / 204800000000000000000), D2 := ((14671878910714285533 : Rat) / 204800000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((2473733901115771 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((538536966910714285533 : Rat) / 204800000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((467869916374999994219 : Rat) / 5120000000000000000000), D4 := ((31726702849285693987 : Rat) / 204800000000000000000), LB := ((11966929163839679 : Rat) / 25000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((13466684590303571423999 : Rat) / 5120000000000000000000), D0 := ((13466684590303571423999 : Rat) / 5120000000000000000000), D1 := ((4161212078303571423999 : Rat) / 5120000000000000000000), D2 := ((370057390303571423999 : Rat) / 5120000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((1861675655551287 : Rat) / 4000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13466684590303571423999 : Rat) / 5120000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((92921899767857141709 : Rat) / 1024000000000000000000), D4 := ((789907153696428064001 : Rat) / 5120000000000000000000), LB := ((1819953203234137 : Rat) / 4000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((13469945007839285709673 : Rat) / 5120000000000000000000), D0 := ((13469945007839285709673 : Rat) / 5120000000000000000000), D1 := ((4164472495839285709673 : Rat) / 5120000000000000000000), D2 := ((373317807839285709673 : Rat) / 5120000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((22370088639692143 : Rat) / 50000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13469945007839285709673 : Rat) / 5120000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((461349081303571422871 : Rat) / 5120000000000000000000), D4 := ((786646736160713778327 : Rat) / 5120000000000000000000), LB := ((1106689861270771 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((13473205425374999995347 : Rat) / 5120000000000000000000), D0 := ((13473205425374999995347 : Rat) / 5120000000000000000000), D1 := ((4167732913374999995347 : Rat) / 5120000000000000000000), D2 := ((376578225374999995347 : Rat) / 5120000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((1102069005341419 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13473205425374999995347 : Rat) / 5120000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((458088663767857137197 : Rat) / 5120000000000000000000), D4 := ((783386318624999492653 : Rat) / 5120000000000000000000), LB := ((11046842643630539 : Rat) / 25000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((13476465842910714281021 : Rat) / 5120000000000000000000), D0 := ((13476465842910714281021 : Rat) / 5120000000000000000000), D1 := ((4170993330910714281021 : Rat) / 5120000000000000000000), D2 := ((379838642910714281021 : Rat) / 5120000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((11145784792613439 : Rat) / 25000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13476465842910714281021 : Rat) / 5120000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((454828246232142851523 : Rat) / 5120000000000000000000), D4 := ((780125901089285206979 : Rat) / 5120000000000000000000), LB := ((4527179751361021 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((2695945252089285713339 : Rat) / 1024000000000000000000), D0 := ((2695945252089285713339 : Rat) / 1024000000000000000000), D1 := ((834850749689285713339 : Rat) / 1024000000000000000000), D2 := ((76619812089285713339 : Rat) / 1024000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((23127547620926947 : Rat) / 50000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2695945252089285713339 : Rat) / 1024000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((451567828696428565849 : Rat) / 5120000000000000000000), D4 := ((155373096710714184261 : Rat) / 1024000000000000000000), LB := ((2376740018601997 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((13482986677982142852369 : Rat) / 5120000000000000000000), D0 := ((13482986677982142852369 : Rat) / 5120000000000000000000), D1 := ((4177514165982142852369 : Rat) / 5120000000000000000000), D2 := ((386359477982142852369 : Rat) / 5120000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((306954372248959 : Rat) / 625000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13482986677982142852369 : Rat) / 5120000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((17932296446428571207 : Rat) / 204800000000000000000), D4 := ((773605066017856635631 : Rat) / 5120000000000000000000), LB := ((637382479527597 : Rat) / 1250000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((13486247095517857138043 : Rat) / 5120000000000000000000), D0 := ((13486247095517857138043 : Rat) / 5120000000000000000000), D1 := ((4180774583517857138043 : Rat) / 5120000000000000000000), D2 := ((389619895517857138043 : Rat) / 5120000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((5317032150629619 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13486247095517857138043 : Rat) / 5120000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((445046993624999994501 : Rat) / 5120000000000000000000), D4 := ((770344648482142349957 : Rat) / 5120000000000000000000), LB := ((5565371316195999 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((13489507513053571423717 : Rat) / 5120000000000000000000), D0 := ((13489507513053571423717 : Rat) / 5120000000000000000000), D1 := ((4184035001053571423717 : Rat) / 5120000000000000000000), D2 := ((392880313053571423717 : Rat) / 5120000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((5844263721984377 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13489507513053571423717 : Rat) / 5120000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((441786576089285708827 : Rat) / 5120000000000000000000), D4 := ((767084230946428064283 : Rat) / 5120000000000000000000), LB := ((153847443935623 : Rat) / 250000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((13492767930589285709391 : Rat) / 5120000000000000000000), D0 := ((13492767930589285709391 : Rat) / 5120000000000000000000), D1 := ((4187295418589285709391 : Rat) / 5120000000000000000000), D2 := ((396140730589285709391 : Rat) / 5120000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((1623615960283653 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13492767930589285709391 : Rat) / 5120000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((438526158553571423153 : Rat) / 5120000000000000000000), D4 := ((763823813410713778609 : Rat) / 5120000000000000000000), LB := ((1373230890048649 : Rat) / 2000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((2699205669624999999013 : Rat) / 1024000000000000000000), D0 := ((2699205669624999999013 : Rat) / 1024000000000000000000), D1 := ((838111167224999999013 : Rat) / 1024000000000000000000), D2 := ((79880229624999999013 : Rat) / 1024000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((145383283005307 : Rat) / 200000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2699205669624999999013 : Rat) / 1024000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((435265741017857137479 : Rat) / 5120000000000000000000), D4 := ((152112679174999898587 : Rat) / 1024000000000000000000), LB := ((7703689625551957 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((1219870931679079 : Rat) / 400000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((1330753079944319 : Rat) / 12500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((2784999067698829 : Rat) / 12500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((35223585264421153 : Rat) / 100000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((989877848229459 : Rat) / 2000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((3255419538538973 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((4104247808100897 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((2511046893667393 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((1502473260260491 : Rat) / 1250000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((220893843930689 : Rat) / 156250000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((3279681472592999 : Rat) / 2000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((5317674537254069 : Rat) / 20000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((794073868641193 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((13831036463707591 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((2034762073619051 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((6877321703446307 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((32972243449613803 : Rat) / 100000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((844664828426811 : Rat) / 400000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((837188176420961 : Rat) / 200000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((1314527450473063 : Rat) / 200000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((29687474371277167 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((955476692275703 : Rat) / 100000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((5363093631214233 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((4021409848352697 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((9755034398539181 : Rat) / 100000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((136811984330357142801 : Rat) / 50000000000000000000), D0 := ((136811984330357142801 : Rat) / 50000000000000000000), D1 := ((45938229330357142801 : Rat) / 50000000000000000000), D2 := ((8915234330357142801 : Rat) / 50000000000000000000), D3 := ((95523811383928577 : Rat) / 6250000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((13899802097659397 : Rat) / 100000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((136811984330357142801 : Rat) / 50000000000000000000), R := ((137576174821428571417 : Rat) / 50000000000000000000), D0 := ((137576174821428571417 : Rat) / 50000000000000000000), D1 := ((46702419821428571417 : Rat) / 50000000000000000000), D2 := ((9679424821428571417 : Rat) / 50000000000000000000), D3 := ((95523811383928577 : Rat) / 3125000000000000000), D4 := ((2412544419642852199 : Rat) / 50000000000000000000), LB := ((245977400864289 : Rat) / 25000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((137576174821428571417 : Rat) / 50000000000000000000), R := ((137767222444196428571 : Rat) / 50000000000000000000), D0 := ((137767222444196428571 : Rat) / 50000000000000000000), D1 := ((46893467444196428571 : Rat) / 50000000000000000000), D2 := ((9870472444196428571 : Rat) / 50000000000000000000), D3 := ((859714302455357193 : Rat) / 25000000000000000000), D4 := ((1648353928571423583 : Rat) / 50000000000000000000), LB := ((1744027047909169 : Rat) / 100000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((137767222444196428571 : Rat) / 50000000000000000000), R := ((5518330802678571429 : Rat) / 2000000000000000000), D0 := ((5518330802678571429 : Rat) / 2000000000000000000), D1 := ((1883380602678571429 : Rat) / 2000000000000000000), D2 := ((402460802678571429 : Rat) / 2000000000000000000), D3 := ((95523811383928577 : Rat) / 2500000000000000000), D4 := ((1457306305803566429 : Rat) / 50000000000000000000), LB := ((2347072198494893 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5518330802678571429 : Rat) / 2000000000000000000), R := ((69026896939174107151 : Rat) / 25000000000000000000), D0 := ((69026896939174107151 : Rat) / 25000000000000000000), D1 := ((23590019439174107151 : Rat) / 25000000000000000000), D2 := ((5078521939174107151 : Rat) / 25000000000000000000), D3 := ((2006000039062500117 : Rat) / 50000000000000000000), D4 := ((50650347321428371 : Rat) / 2000000000000000000), LB := ((31126615682277037 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((69026896939174107151 : Rat) / 25000000000000000000), R := ((276203111568080357181 : Rat) / 100000000000000000000), D0 := ((276203111568080357181 : Rat) / 100000000000000000000), D1 := ((94455601568080357181 : Rat) / 100000000000000000000), D2 := ((20409611568080357181 : Rat) / 100000000000000000000), D3 := ((4107523889508928811 : Rat) / 100000000000000000000), D4 := ((585367435825890349 : Rat) / 25000000000000000000), LB := ((5547939134387253 : Rat) / 1250000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((276203111568080357181 : Rat) / 100000000000000000000), R := ((138149317689732142879 : Rat) / 50000000000000000000), D0 := ((138149317689732142879 : Rat) / 50000000000000000000), D1 := ((47275562689732142879 : Rat) / 50000000000000000000), D2 := ((10252567689732142879 : Rat) / 50000000000000000000), D3 := ((1050761925223214347 : Rat) / 25000000000000000000), D4 := ((2245945931919632819 : Rat) / 100000000000000000000), LB := ((5769502588238301 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((138149317689732142879 : Rat) / 50000000000000000000), R := ((55278831838169642867 : Rat) / 20000000000000000000), D0 := ((55278831838169642867 : Rat) / 20000000000000000000), D1 := ((18929329838169642867 : Rat) / 20000000000000000000), D2 := ((4120131838169642867 : Rat) / 20000000000000000000), D3 := ((859714302455357193 : Rat) / 20000000000000000000), D4 := ((1075211060267852121 : Rat) / 50000000000000000000), LB := ((555058123754143 : Rat) / 1250000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((55278831838169642867 : Rat) / 20000000000000000000), R := ((552883842193080357247 : Rat) / 200000000000000000000), D0 := ((552883842193080357247 : Rat) / 200000000000000000000), D1 := ((189388822193080357247 : Rat) / 200000000000000000000), D2 := ((41296842193080357247 : Rat) / 200000000000000000000), D3 := ((8692666835937500507 : Rat) / 200000000000000000000), D4 := ((410979661830355133 : Rat) / 20000000000000000000), LB := ((3669815336100113 : Rat) / 2000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((552883842193080357247 : Rat) / 200000000000000000000), R := ((4320151296909877233 : Rat) / 1562500000000000000), D0 := ((4320151296909877233 : Rat) / 1562500000000000000), D1 := ((1480346453159877233 : Rat) / 1562500000000000000), D2 := ((323377859409877233 : Rat) / 1562500000000000000), D3 := ((2197047661830357271 : Rat) / 50000000000000000000), D4 := ((4014272806919622753 : Rat) / 200000000000000000000), LB := ((11302610699885363 : Rat) / 10000000000000000000) }
]

def block181RightChunk000L : Rat := ((44547390625000000039 : Rat) / 25000000000000000000)
def block181RightChunk000R : Rat := ((4320151296909877233 : Rat) / 1562500000000000000)

def block181RightChunk000Certificate : Bool :=
  allBoxesValid block181RightChunk000 &&
  coversFromBool block181RightChunk000 block181RightChunk000L block181RightChunk000R

theorem block181RightChunk000Certificate_eq_true :
    block181RightChunk000Certificate = true := by
  native_decide

def block181RightChunk001 : List RatBox := [
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4320151296909877233 : Rat) / 1562500000000000000), R := ((553074889815848214401 : Rat) / 200000000000000000000), D0 := ((553074889815848214401 : Rat) / 200000000000000000000), D1 := ((189579869815848214401 : Rat) / 200000000000000000000), D2 := ((41487889815848214401 : Rat) / 200000000000000000000), D3 := ((8883714458705357661 : Rat) / 200000000000000000000), D4 := ((122460906110490443 : Rat) / 6250000000000000000), LB := ((12534438774571 : Rat) / 25000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553074889815848214401 : Rat) / 200000000000000000000), R := ((1106245303443080357379 : Rat) / 400000000000000000000), D0 := ((1106245303443080357379 : Rat) / 400000000000000000000), D1 := ((379255263443080357379 : Rat) / 400000000000000000000), D2 := ((83071303443080357379 : Rat) / 400000000000000000000), D3 := ((17862952728794643899 : Rat) / 400000000000000000000), D4 := ((3823225184151765599 : Rat) / 200000000000000000000), LB := ((14150636947111161 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1106245303443080357379 : Rat) / 400000000000000000000), R := ((276585206813616071489 : Rat) / 100000000000000000000), D0 := ((276585206813616071489 : Rat) / 100000000000000000000), D1 := ((94837696813616071489 : Rat) / 100000000000000000000), D2 := ((20791706813616071489 : Rat) / 100000000000000000000), D3 := ((4489619135044643119 : Rat) / 100000000000000000000), D4 := ((7550926556919602621 : Rat) / 400000000000000000000), LB := ((5823030205471813 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((276585206813616071489 : Rat) / 100000000000000000000), R := ((1106436351065848214533 : Rat) / 400000000000000000000), D0 := ((1106436351065848214533 : Rat) / 400000000000000000000), D1 := ((379446311065848214533 : Rat) / 400000000000000000000), D2 := ((83262351065848214533 : Rat) / 400000000000000000000), D3 := ((18054000351562501053 : Rat) / 400000000000000000000), D4 := ((1863850686383918511 : Rat) / 100000000000000000000), LB := ((584157797312683 : Rat) / 625000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1106436351065848214533 : Rat) / 400000000000000000000), R := ((110653187487723214311 : Rat) / 40000000000000000000), D0 := ((110653187487723214311 : Rat) / 40000000000000000000), D1 := ((37954183487723214311 : Rat) / 40000000000000000000), D2 := ((8335787487723214311 : Rat) / 40000000000000000000), D3 := ((1814952416294642963 : Rat) / 40000000000000000000), D4 := ((7359878934151745467 : Rat) / 400000000000000000000), LB := ((3627746020447853 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((110653187487723214311 : Rat) / 40000000000000000000), R := ((1106627398688616071687 : Rat) / 400000000000000000000), D0 := ((1106627398688616071687 : Rat) / 400000000000000000000), D1 := ((379637358688616071687 : Rat) / 400000000000000000000), D2 := ((83453398688616071687 : Rat) / 400000000000000000000), D3 := ((18245047974330358207 : Rat) / 400000000000000000000), D4 := ((726435512276781689 : Rat) / 40000000000000000000), LB := ((5376588092284029 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1106627398688616071687 : Rat) / 400000000000000000000), R := ((138340365312500000033 : Rat) / 50000000000000000000), D0 := ((138340365312500000033 : Rat) / 50000000000000000000), D1 := ((47466610312500000033 : Rat) / 50000000000000000000), D2 := ((10443615312500000033 : Rat) / 50000000000000000000), D3 := ((286571434151785731 : Rat) / 6250000000000000000), D4 := ((7168831311383888313 : Rat) / 400000000000000000000), LB := ((3713610500974407 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((138340365312500000033 : Rat) / 50000000000000000000), R := ((1106818446311383928841 : Rat) / 400000000000000000000), D0 := ((1106818446311383928841 : Rat) / 400000000000000000000), D1 := ((379828406311383928841 : Rat) / 400000000000000000000), D2 := ((83644446311383928841 : Rat) / 400000000000000000000), D3 := ((18436095597098215361 : Rat) / 400000000000000000000), D4 := ((884163437499994967 : Rat) / 50000000000000000000), LB := ((454107428439543 : Rat) / 2000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1106818446311383928841 : Rat) / 400000000000000000000), R := ((553456985061383928709 : Rat) / 200000000000000000000), D0 := ((553456985061383928709 : Rat) / 200000000000000000000), D1 := ((189961965061383928709 : Rat) / 200000000000000000000), D2 := ((41869985061383928709 : Rat) / 200000000000000000000), D3 := ((9265809704241071969 : Rat) / 200000000000000000000), D4 := ((6977783688616031159 : Rat) / 400000000000000000000), LB := ((10515352821971469 : Rat) / 100000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553456985061383928709 : Rat) / 200000000000000000000), R := ((221401898786830357199 : Rat) / 80000000000000000000), D0 := ((221401898786830357199 : Rat) / 80000000000000000000), D1 := ((76003890786830357199 : Rat) / 80000000000000000000), D2 := ((16767098786830357199 : Rat) / 80000000000000000000), D3 := ((3725428643973214503 : Rat) / 80000000000000000000), D4 := ((3441129938616051291 : Rat) / 200000000000000000000), LB := ((6097130965887487 : Rat) / 1000000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((221401898786830357199 : Rat) / 80000000000000000000), R := ((2214114511679687500567 : Rat) / 800000000000000000000), D0 := ((2214114511679687500567 : Rat) / 800000000000000000000), D1 := ((760134431679687500567 : Rat) / 800000000000000000000), D2 := ((167766511679687500567 : Rat) / 800000000000000000000), D3 := ((37349810251116073607 : Rat) / 800000000000000000000), D4 := ((1357347213169634801 : Rat) / 80000000000000000000), LB := ((6425422687961757 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2214114511679687500567 : Rat) / 800000000000000000000), R := ((276776254436383928643 : Rat) / 100000000000000000000), D0 := ((276776254436383928643 : Rat) / 100000000000000000000), D1 := ((95028744436383928643 : Rat) / 100000000000000000000), D2 := ((20982754436383928643 : Rat) / 100000000000000000000), D3 := ((4680666757812500273 : Rat) / 100000000000000000000), D4 := ((13477948320312419433 : Rat) / 800000000000000000000), LB := ((1530970436206397 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((276776254436383928643 : Rat) / 100000000000000000000), R := ((2214305559302455357721 : Rat) / 800000000000000000000), D0 := ((2214305559302455357721 : Rat) / 800000000000000000000), D1 := ((760325479302455357721 : Rat) / 800000000000000000000), D2 := ((167957559302455357721 : Rat) / 800000000000000000000), D3 := ((37540857873883930761 : Rat) / 800000000000000000000), D4 := ((1672803063616061357 : Rat) / 100000000000000000000), LB := ((1470617134713137 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2214305559302455357721 : Rat) / 800000000000000000000), R := ((1107200541556919643149 : Rat) / 400000000000000000000), D0 := ((1107200541556919643149 : Rat) / 400000000000000000000), D1 := ((380210501556919643149 : Rat) / 400000000000000000000), D2 := ((84026541556919643149 : Rat) / 400000000000000000000), D3 := ((18818190842633929669 : Rat) / 400000000000000000000), D4 := ((13286900697544562279 : Rat) / 800000000000000000000), LB := ((5701818639213263 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1107200541556919643149 : Rat) / 400000000000000000000), R := ((17715972855401785719 : Rat) / 6400000000000000000), D0 := ((17715972855401785719 : Rat) / 6400000000000000000), D1 := ((6084132215401785719 : Rat) / 6400000000000000000), D2 := ((1345188855401785719 : Rat) / 6400000000000000000), D3 := ((7546381099330357583 : Rat) / 160000000000000000000), D4 := ((6595688443080316851 : Rat) / 400000000000000000000), LB := ((5582582947388781 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17715972855401785719 : Rat) / 6400000000000000000), R := ((553648032684151785863 : Rat) / 200000000000000000000), D0 := ((553648032684151785863 : Rat) / 200000000000000000000), D1 := ((190153012684151785863 : Rat) / 200000000000000000000), D2 := ((42061032684151785863 : Rat) / 200000000000000000000), D3 := ((9456857327008929123 : Rat) / 200000000000000000000), D4 := ((104766824598213641 : Rat) / 6400000000000000000), LB := ((2762714058641147 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553648032684151785863 : Rat) / 200000000000000000000), R := ((2214687654547991072029 : Rat) / 800000000000000000000), D0 := ((2214687654547991072029 : Rat) / 800000000000000000000), D1 := ((760707574547991072029 : Rat) / 800000000000000000000), D2 := ((168339654547991072029 : Rat) / 800000000000000000000), D3 := ((37922953119419645069 : Rat) / 800000000000000000000), D4 := ((3250082315848194137 : Rat) / 200000000000000000000), LB := ((5531036990466531 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2214687654547991072029 : Rat) / 800000000000000000000), R := ((1107391589179687500303 : Rat) / 400000000000000000000), D0 := ((1107391589179687500303 : Rat) / 400000000000000000000), D1 := ((380401549179687500303 : Rat) / 400000000000000000000), D2 := ((84217589179687500303 : Rat) / 400000000000000000000), D3 := ((19009238465401786823 : Rat) / 400000000000000000000), D4 := ((12904805452008847971 : Rat) / 800000000000000000000), LB := ((280005452340637 : Rat) / 500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1107391589179687500303 : Rat) / 400000000000000000000), R := ((2214878702170758929183 : Rat) / 800000000000000000000), D0 := ((2214878702170758929183 : Rat) / 800000000000000000000), D1 := ((760898622170758929183 : Rat) / 800000000000000000000), D2 := ((168530702170758929183 : Rat) / 800000000000000000000), D3 := ((38114000742187502223 : Rat) / 800000000000000000000), D4 := ((6404640820312459697 : Rat) / 400000000000000000000), LB := ((573336087148657 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2214878702170758929183 : Rat) / 800000000000000000000), R := ((13843588912388392861 : Rat) / 5000000000000000000), D0 := ((13843588912388392861 : Rat) / 5000000000000000000), D1 := ((4756213412388392861 : Rat) / 5000000000000000000), D2 := ((1053913912388392861 : Rat) / 5000000000000000000), D3 := ((95523811383928577 : Rat) / 2000000000000000000), D4 := ((12713757829240990817 : Rat) / 800000000000000000000), LB := ((2965763319379977 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13843588912388392861 : Rat) / 5000000000000000000), R := ((2215069749793526786337 : Rat) / 800000000000000000000), D0 := ((2215069749793526786337 : Rat) / 800000000000000000000), D1 := ((761089669793526786337 : Rat) / 800000000000000000000), D2 := ((168721749793526786337 : Rat) / 800000000000000000000), D3 := ((38305048364955359377 : Rat) / 800000000000000000000), D4 := ((78863962611606639 : Rat) / 5000000000000000000), LB := ((6195358613461099 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2215069749793526786337 : Rat) / 800000000000000000000), R := ((1107582636802455357457 : Rat) / 400000000000000000000), D0 := ((1107582636802455357457 : Rat) / 400000000000000000000), D1 := ((380592596802455357457 : Rat) / 400000000000000000000), D2 := ((84408636802455357457 : Rat) / 400000000000000000000), D3 := ((19200286088169643977 : Rat) / 400000000000000000000), D4 := ((12522710206473133663 : Rat) / 800000000000000000000), LB := ((6525627670703749 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1107582636802455357457 : Rat) / 400000000000000000000), R := ((2215260797416294643491 : Rat) / 800000000000000000000), D0 := ((2215260797416294643491 : Rat) / 800000000000000000000), D1 := ((761280717416294643491 : Rat) / 800000000000000000000), D2 := ((168912797416294643491 : Rat) / 800000000000000000000), D3 := ((38496095987723216531 : Rat) / 800000000000000000000), D4 := ((6213593197544602543 : Rat) / 400000000000000000000), LB := ((432695239675103 : Rat) / 625000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2215260797416294643491 : Rat) / 800000000000000000000), R := ((553839080306919643017 : Rat) / 200000000000000000000), D0 := ((553839080306919643017 : Rat) / 200000000000000000000), D1 := ((190344060306919643017 : Rat) / 200000000000000000000), D2 := ((42252080306919643017 : Rat) / 200000000000000000000), D3 := ((9647904949776786277 : Rat) / 200000000000000000000), D4 := ((12331662583705276509 : Rat) / 800000000000000000000), LB := ((738865683794887 : Rat) / 1000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553839080306919643017 : Rat) / 200000000000000000000), R := ((1107773684425223214611 : Rat) / 400000000000000000000), D0 := ((1107773684425223214611 : Rat) / 400000000000000000000), D1 := ((380783644425223214611 : Rat) / 400000000000000000000), D2 := ((84599684425223214611 : Rat) / 400000000000000000000), D3 := ((19391333710937501131 : Rat) / 400000000000000000000), D4 := ((3059034693080336983 : Rat) / 200000000000000000000), LB := ((4794325620882667 : Rat) / 50000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1107773684425223214611 : Rat) / 400000000000000000000), R := ((276967302059151785797 : Rat) / 100000000000000000000), D0 := ((276967302059151785797 : Rat) / 100000000000000000000), D1 := ((95219792059151785797 : Rat) / 100000000000000000000), D2 := ((21173802059151785797 : Rat) / 100000000000000000000), D3 := ((4871714380580357427 : Rat) / 100000000000000000000), D4 := ((6022545574776745389 : Rat) / 400000000000000000000), LB := ((22593720596270073 : Rat) / 100000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((276967302059151785797 : Rat) / 100000000000000000000), R := ((221592946409598214353 : Rat) / 80000000000000000000), D0 := ((221592946409598214353 : Rat) / 80000000000000000000), D1 := ((76194938409598214353 : Rat) / 80000000000000000000), D2 := ((16958146409598214353 : Rat) / 80000000000000000000), D3 := ((3916476266741071657 : Rat) / 80000000000000000000), D4 := ((1481755440848204203 : Rat) / 100000000000000000000), LB := ((9614086670567401 : Rat) / 25000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((221592946409598214353 : Rat) / 80000000000000000000), R := ((554030127929687500171 : Rat) / 200000000000000000000), D0 := ((554030127929687500171 : Rat) / 200000000000000000000), D1 := ((190535107929687500171 : Rat) / 200000000000000000000), D2 := ((42443127929687500171 : Rat) / 200000000000000000000), D3 := ((9838952572544643431 : Rat) / 200000000000000000000), D4 := ((1166299590401777647 : Rat) / 80000000000000000000), LB := ((715636347529483 : Rat) / 1250000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((554030127929687500171 : Rat) / 200000000000000000000), R := ((1108155779670758928919 : Rat) / 400000000000000000000), D0 := ((1108155779670758928919 : Rat) / 400000000000000000000), D1 := ((381165739670758928919 : Rat) / 400000000000000000000), D2 := ((84981779670758928919 : Rat) / 400000000000000000000), D3 := ((19773428956473215439 : Rat) / 400000000000000000000), D4 := ((2867987070312479829 : Rat) / 200000000000000000000), LB := ((7905566436322009 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1108155779670758928919 : Rat) / 400000000000000000000), R := ((138531412935267857187 : Rat) / 50000000000000000000), D0 := ((138531412935267857187 : Rat) / 50000000000000000000), D1 := ((47657657935267857187 : Rat) / 50000000000000000000), D2 := ((10634662935267857187 : Rat) / 50000000000000000000), D3 := ((1241809547991071501 : Rat) / 25000000000000000000), D4 := ((5640450329241031081 : Rat) / 400000000000000000000), LB := ((10395300440289579 : Rat) / 10000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((138531412935267857187 : Rat) / 50000000000000000000), R := ((1108346827293526786073 : Rat) / 400000000000000000000), D0 := ((1108346827293526786073 : Rat) / 400000000000000000000), D1 := ((381356787293526786073 : Rat) / 400000000000000000000), D2 := ((85172827293526786073 : Rat) / 400000000000000000000), D3 := ((19964476579241072593 : Rat) / 400000000000000000000), D4 := ((693115814732137813 : Rat) / 50000000000000000000), LB := ((3300742715576649 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1108346827293526786073 : Rat) / 400000000000000000000), R := ((22168847022098214293 : Rat) / 8000000000000000000), D0 := ((22168847022098214293 : Rat) / 8000000000000000000), D1 := ((7629046222098214293 : Rat) / 8000000000000000000), D2 := ((1705367022098214293 : Rat) / 8000000000000000000), D3 := ((2006000039062500117 : Rat) / 40000000000000000000), D4 := ((5449402706473173927 : Rat) / 400000000000000000000), LB := ((326754473412183 : Rat) / 200000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((22168847022098214293 : Rat) / 8000000000000000000), R := ((277158349681919642951 : Rat) / 100000000000000000000), D0 := ((277158349681919642951 : Rat) / 100000000000000000000), D1 := ((95410839681919642951 : Rat) / 100000000000000000000), D2 := ((21364849681919642951 : Rat) / 100000000000000000000), D3 := ((5062762003348214581 : Rat) / 100000000000000000000), D4 := ((107077577901784907 : Rat) / 8000000000000000000), LB := ((1561673986683887 : Rat) / 2500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((277158349681919642951 : Rat) / 100000000000000000000), R := ((554412223175223214479 : Rat) / 200000000000000000000), D0 := ((554412223175223214479 : Rat) / 200000000000000000000), D1 := ((190917203175223214479 : Rat) / 200000000000000000000), D2 := ((42825223175223214479 : Rat) / 200000000000000000000), D3 := ((10221047818080357739 : Rat) / 200000000000000000000), D4 := ((1290707818080347049 : Rat) / 100000000000000000000), LB := ((11456519781607 : Rat) / 8000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((554412223175223214479 : Rat) / 200000000000000000000), R := ((34656734186662946441 : Rat) / 12500000000000000000), D0 := ((34656734186662946441 : Rat) / 12500000000000000000), D1 := ((11938295436662946441 : Rat) / 12500000000000000000), D2 := ((2682546686662946441 : Rat) / 12500000000000000000), D3 := ((2579142907366071579 : Rat) / 50000000000000000000), D4 := ((2485891824776765521 : Rat) / 200000000000000000000), LB := ((11934917765087927 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((34656734186662946441 : Rat) / 12500000000000000000), R := ((55469879460937500021 : Rat) / 20000000000000000000), D0 := ((55469879460937500021 : Rat) / 20000000000000000000), D1 := ((19120377460937500021 : Rat) / 20000000000000000000), D2 := ((4311179460937500021 : Rat) / 20000000000000000000), D3 := ((1050761925223214347 : Rat) / 20000000000000000000), D4 := ((149398000837052309 : Rat) / 12500000000000000000), LB := ((4225034368550151 : Rat) / 5000000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((55469879460937500021 : Rat) / 20000000000000000000), R := ((138722460558035714341 : Rat) / 50000000000000000000), D0 := ((138722460558035714341 : Rat) / 50000000000000000000), D1 := ((47848705558035714341 : Rat) / 50000000000000000000), D2 := ((10825710558035714341 : Rat) / 50000000000000000000), D3 := ((668666679687500039 : Rat) / 12500000000000000000), D4 := ((219932039062497979 : Rat) / 20000000000000000000), LB := ((452148164761329 : Rat) / 125000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((138722460558035714341 : Rat) / 50000000000000000000), R := ((69408992184709821459 : Rat) / 25000000000000000000), D0 := ((69408992184709821459 : Rat) / 25000000000000000000), D1 := ((23972114684709821459 : Rat) / 25000000000000000000), D2 := ((5460617184709821459 : Rat) / 25000000000000000000), D3 := ((2770190530133928733 : Rat) / 50000000000000000000), D4 := ((502068191964280659 : Rat) / 50000000000000000000), LB := ((201918476175611 : Rat) / 100000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((69408992184709821459 : Rat) / 25000000000000000000), R := ((27782701636160714299 : Rat) / 10000000000000000000), D0 := ((27782701636160714299 : Rat) / 10000000000000000000), D1 := ((9607950636160714299 : Rat) / 10000000000000000000), D2 := ((2203351636160714299 : Rat) / 10000000000000000000), D3 := ((286571434151785731 : Rat) / 5000000000000000000), D4 := ((203272190290176041 : Rat) / 25000000000000000000), LB := ((6081900966976139 : Rat) / 500000000000000000) },
  { w1 := ((1783617053519739 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8709504852769201 : Rat) / 50000000000000000), w4 := ((4828890932775437 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27782701636160714299 : Rat) / 10000000000000000000), R := ((139104555803571428649 : Rat) / 50000000000000000000), D0 := ((139104555803571428649 : Rat) / 50000000000000000000), D1 := ((48230800803571428649 : Rat) / 50000000000000000000), D2 := ((11207805803571428649 : Rat) / 50000000000000000000), D3 := ((95523811383928577 : Rat) / 1562500000000000000), D4 := ((62204113839284701 : Rat) / 10000000000000000000), LB := ((8978682298354579 : Rat) / 500000000000000000) }
]

def block181RightChunk001L : Rat := ((4320151296909877233 : Rat) / 1562500000000000000)
def block181RightChunk001R : Rat := ((139104555803571428649 : Rat) / 50000000000000000000)

def block181RightChunk001Certificate : Bool :=
  allBoxesValid block181RightChunk001 &&
  coversFromBool block181RightChunk001 block181RightChunk001L block181RightChunk001R

theorem block181RightChunk001Certificate_eq_true :
    block181RightChunk001Certificate = true := by
  native_decide

def block181RightChainCertificate : Bool :=
  decide (
    block181RightL = ((44547390625000000039 : Rat) / 25000000000000000000) /\
    ((4320151296909877233 : Rat) / 1562500000000000000) = ((4320151296909877233 : Rat) / 1562500000000000000) /\
    ((139104555803571428649 : Rat) / 50000000000000000000) = block181RightR)

theorem block181RightChainCertificate_eq_true :
    block181RightChainCertificate = true := by
  native_decide

def block181LeftBoxCount : Nat := boxCount block181LeftBoxes
def block181RightBoxCount : Nat := 140

def block181_rational_certificate : Prop :=
    block181LeftCertificate = true /\
    block181RightChainCertificate = true /\
    block181RightChunk000Certificate = true /\
    block181RightChunk001Certificate = true

theorem block181_rational_certificate_proof :
    block181_rational_certificate := by
  exact ⟨block181LeftCertificate_eq_true, block181RightChainCertificate_eq_true, block181RightChunk000Certificate_eq_true, block181RightChunk001Certificate_eq_true⟩

end Block181
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block181

open Set

def block181W1 : Rat := ((1783617053519739 : Rat) / 1000000000000000)
def block181W2 : Rat := (0 : Rat)
def block181W3 : Rat := ((8709504852769201 : Rat) / 50000000000000000)
def block181W4 : Rat := ((4828890932775437 : Rat) / 50000000000000000)
def block181S1 : Rat := ((18174751 : Rat) / 10000000)
def block181S2 : Rat := ((511587 : Rat) / 200000)
def block181S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block181S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block181V (y : ℝ) : ℝ :=
  ratPotential block181W1 block181W2 block181W3 block181W4 block181S1 block181S2 block181S3 block181S4 y

def block181LeftParamsCertificate : Bool :=
  allBoxesSameParams block181LeftBoxes block181W1 block181W2 block181W3 block181W4 block181S1 block181S2 block181S3 block181S4

theorem block181LeftParamsCertificate_eq_true :
    block181LeftParamsCertificate = true := by
  native_decide

theorem block181_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block181LeftL : ℝ) (block181LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block181S1 : ℝ))
    (hy2ne : y ≠ (block181S2 : ℝ))
    (hy3ne : y ≠ (block181S3 : ℝ))
    (hy4ne : y ≠ (block181S4 : ℝ)) :
    0 < block181V y := by
  have hcert := block181LeftCertificate_eq_true
  unfold block181LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block181LeftBoxes) (lo := block181LeftL) (hi := block181LeftR)
    (w1 := block181W1) (w2 := block181W2) (w3 := block181W3) (w4 := block181W4)
    (s1 := block181S1) (s2 := block181S2) (s3 := block181S3) (s4 := block181S4)
    hboxes hcover block181LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block181RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block181RightChunk000 block181W1 block181W2 block181W3 block181W4 block181S1 block181S2 block181S3 block181S4

theorem block181RightChunk000ParamsCertificate_eq_true :
    block181RightChunk000ParamsCertificate = true := by
  native_decide

theorem block181_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block181RightChunk000L : ℝ) (block181RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block181S1 : ℝ))
    (hy2ne : y ≠ (block181S2 : ℝ))
    (hy3ne : y ≠ (block181S3 : ℝ))
    (hy4ne : y ≠ (block181S4 : ℝ)) :
    0 < block181V y := by
  have hcert := block181RightChunk000Certificate_eq_true
  unfold block181RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block181RightChunk000) (lo := block181RightChunk000L) (hi := block181RightChunk000R)
    (w1 := block181W1) (w2 := block181W2) (w3 := block181W3) (w4 := block181W4)
    (s1 := block181S1) (s2 := block181S2) (s3 := block181S3) (s4 := block181S4)
    hboxes hcover block181RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block181RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block181RightChunk001 block181W1 block181W2 block181W3 block181W4 block181S1 block181S2 block181S3 block181S4

theorem block181RightChunk001ParamsCertificate_eq_true :
    block181RightChunk001ParamsCertificate = true := by
  native_decide

theorem block181_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block181RightChunk001L : ℝ) (block181RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block181S1 : ℝ))
    (hy2ne : y ≠ (block181S2 : ℝ))
    (hy3ne : y ≠ (block181S3 : ℝ))
    (hy4ne : y ≠ (block181S4 : ℝ)) :
    0 < block181V y := by
  have hcert := block181RightChunk001Certificate_eq_true
  unfold block181RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block181RightChunk001) (lo := block181RightChunk001L) (hi := block181RightChunk001R)
    (w1 := block181W1) (w2 := block181W2) (w3 := block181W3) (w4 := block181W4)
    (s1 := block181S1) (s2 := block181S2) (s3 := block181S3) (s4 := block181S4)
    hboxes hcover block181RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block181_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block181RightL : ℝ) (block181RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block181S1 : ℝ))
    (hy2ne : y ≠ (block181S2 : ℝ))
    (hy3ne : y ≠ (block181S3 : ℝ))
    (hy4ne : y ≠ (block181S4 : ℝ)) :
    0 < block181V y := by
  by_cases h0 : y ≤ (block181RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block181RightChunk000L : ℝ) (block181RightChunk000R : ℝ) := by
      have hL : (block181RightChunk000L : ℝ) = (block181RightL : ℝ) := by
        norm_num [block181RightChunk000L, block181RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block181_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block181RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block181RightChunk001L : ℝ) = (block181RightChunk000R : ℝ) := by
      norm_num [block181RightChunk001L, block181RightChunk000R]
    have hR : (block181RightChunk001R : ℝ) = (block181RightR : ℝ) := by
      norm_num [block181RightChunk001R, block181RightR]
    have hyc : y ∈ Icc (block181RightChunk001L : ℝ) (block181RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block181_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block181_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block181LeftL : ℝ) (block181LeftR : ℝ) →
    y ≠ 0 → y ≠ (block181S1 : ℝ) → y ≠ (block181S2 : ℝ) →
    y ≠ (block181S3 : ℝ) → y ≠ (block181S4 : ℝ) → 0 < block181V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block181RightL : ℝ) (block181RightR : ℝ) →
    y ≠ 0 → y ≠ (block181S1 : ℝ) → y ≠ (block181S2 : ℝ) →
    y ≠ (block181S3 : ℝ) → y ≠ (block181S4 : ℝ) → 0 < block181V y)

theorem block181_reallog_certificate_proof :
    block181_reallog_certificate := by
  exact ⟨block181_left_V_pos, block181_right_V_pos⟩

end Block181
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block181.block181V
#check Erdos1038Lean.M1817475.Block181.block181_left_V_pos
#check Erdos1038Lean.M1817475.Block181.block181_right_V_pos
#check Erdos1038Lean.M1817475.Block181.block181_reallog_certificate_proof
