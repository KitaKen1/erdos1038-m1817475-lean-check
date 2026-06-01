/-
Self-contained Lean4Web paste file.
Block 336 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block336

def block336LeftL : Rat := ((37579725446428571573 : Rat) / 50000000000000000000)
def block336LeftR : Rat := ((2349343750000000009 : Rat) / 3125000000000000000)
def block336RightL : Rat := ((87579725446428571573 : Rat) / 50000000000000000000)
def block336RightR : Rat := ((8599343750000000009 : Rat) / 3125000000000000000)

def block336LeftBoxes : List RatBox := [
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37579725446428571573 : Rat) / 50000000000000000000), R := ((2349343750000000009 : Rat) / 3125000000000000000), D0 := ((2349343750000000009 : Rat) / 3125000000000000000), D1 := ((53294029553571428427 : Rat) / 50000000000000000000), D2 := ((90317024553571428427 : Rat) / 50000000000000000000), D3 := ((47992665892857142789 : Rat) / 25000000000000000000), D4 := ((4041551239285714081 : Rat) / 2000000000000000000), LB := ((3218020200449631 : Rat) / 500000000000000000) }
]

def block336LeftCertificate : Bool :=
  allBoxesValid block336LeftBoxes &&
  coversFromBool block336LeftBoxes block336LeftL block336LeftR

theorem block336LeftCertificate_eq_true :
    block336LeftCertificate = true := by
  native_decide

def block336RightChunk000 : List RatBox := [
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87579725446428571573 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3294029553571428427 : Rat) / 50000000000000000000), D2 := ((40317024553571428427 : Rat) / 50000000000000000000), D3 := ((22992665892857142789 : Rat) / 25000000000000000000), D4 := ((2041551239285714081 : Rat) / 2000000000000000000), LB := ((1230187791279143 : Rat) / 625000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42691302232142857151 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((1908142283090849 : Rat) / 10000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24179804732142857151 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((2461583379524419 : Rat) / 20000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19551930357142857151 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((409252368789969 : Rat) / 5000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17237993169642857151 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((10577852152265421 : Rat) / 500000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14924055982142857151 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((19750661999329733 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13767087388392857151 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((1130537785201069 : Rat) / 50000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((13188603091517857151 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((853696380592869 : Rat) / 62500000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12610118794642857151 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((5775254872939561 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((12031634497767857151 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((1263782722084203 : Rat) / 125000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11742392349330357151 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((1776634477129821 : Rat) / 250000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11453150200892857151 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((276562174748779 : Rat) / 62500000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11163908052455357151 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((4162251847072751 : Rat) / 2000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10874665904017857151 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((9268986161550807 : Rat) / 100000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10585423755580357151 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((3842656573119413 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10440802681361607151 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((791151864310613 : Rat) / 250000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10296181607142857151 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((6474793962880851 : Rat) / 2500000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10151560532924107151 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((2122197691747929 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((10006939458705357151 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((8826866310738257 : Rat) / 5000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9862318384486607151 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((3809309098955771 : Rat) / 2500000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9717697310267857151 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((7009638867797041 : Rat) / 5000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9573076236049107151 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((14051180372645633 : Rat) / 10000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9428455161830357151 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((7694719593615701 : Rat) / 5000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9283834087611607151 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((4524119708728333 : Rat) / 2500000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9139213013392857151 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((5560390901987039 : Rat) / 2500000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8994591939174107151 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((2790189681745159 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8849970864955357151 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((351639598659953 : Rat) / 100000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8705349790736607151 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((2206257874306783 : Rat) / 500000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8560728716517857151 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((3929801545195233 : Rat) / 10000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8271486568080357151 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((15888903805589827 : Rat) / 5000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7982244419642857151 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((3431950884817847 : Rat) / 500000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7693002271205357151 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((5811967053800507 : Rat) / 500000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7403760122767857151 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((7840491825053059 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6825275825892857151 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((6573887403271889 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028842307232142857151 : Rat) / 400000000000000000000), D0 := ((1028842307232142857151 : Rat) / 400000000000000000000), D1 := ((301852267232142857151 : Rat) / 400000000000000000000), D2 := ((5668307232142857151 : Rat) / 400000000000000000000), D3 := ((5668307232142857151 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((4753571090216899 : Rat) / 100000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028842307232142857151 : Rat) / 400000000000000000000), R := ((517255307232142857151 : Rat) / 200000000000000000000), D0 := ((517255307232142857151 : Rat) / 200000000000000000000), D1 := ((153760287232142857151 : Rat) / 200000000000000000000), D2 := ((5668307232142857151 : Rat) / 200000000000000000000), D3 := ((39678150625000000057 : Rat) / 400000000000000000000), D4 := ((80105744196428531633 : Rat) / 400000000000000000000), LB := ((2049710824108203 : Rat) / 100000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517255307232142857151 : Rat) / 200000000000000000000), R := ((1040178921696428571453 : Rat) / 400000000000000000000), D0 := ((1040178921696428571453 : Rat) / 400000000000000000000), D1 := ((313188881696428571453 : Rat) / 400000000000000000000), D2 := ((17004921696428571453 : Rat) / 400000000000000000000), D3 := ((17004921696428571453 : Rat) / 200000000000000000000), D4 := ((37218718482142837241 : Rat) / 200000000000000000000), LB := ((11122639722109251 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1040178921696428571453 : Rat) / 400000000000000000000), R := ((261461807232142857151 : Rat) / 100000000000000000000), D0 := ((261461807232142857151 : Rat) / 100000000000000000000), D1 := ((79714297232142857151 : Rat) / 100000000000000000000), D2 := ((5668307232142857151 : Rat) / 100000000000000000000), D3 := ((5668307232142857151 : Rat) / 80000000000000000000), D4 := ((68769129732142817331 : Rat) / 400000000000000000000), LB := ((12549402503390317 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261461807232142857151 : Rat) / 100000000000000000000), R := ((210303107232142857151 : Rat) / 80000000000000000000), D0 := ((210303107232142857151 : Rat) / 80000000000000000000), D1 := ((64905099232142857151 : Rat) / 80000000000000000000), D2 := ((5668307232142857151 : Rat) / 80000000000000000000), D3 := ((5668307232142857151 : Rat) / 100000000000000000000), D4 := ((3155041124999998009 : Rat) / 20000000000000000000), LB := ((1210613532310173 : Rat) / 50000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((210303107232142857151 : Rat) / 80000000000000000000), R := ((528591921696428571453 : Rat) / 200000000000000000000), D0 := ((528591921696428571453 : Rat) / 200000000000000000000), D1 := ((165096901696428571453 : Rat) / 200000000000000000000), D2 := ((17004921696428571453 : Rat) / 200000000000000000000), D3 := ((17004921696428571453 : Rat) / 400000000000000000000), D4 := ((57432515267857103029 : Rat) / 400000000000000000000), LB := ((4858889190624077 : Rat) / 100000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528591921696428571453 : Rat) / 200000000000000000000), R := ((133565057232142857151 : Rat) / 50000000000000000000), D0 := ((133565057232142857151 : Rat) / 50000000000000000000), D1 := ((42691302232142857151 : Rat) / 50000000000000000000), D2 := ((5668307232142857151 : Rat) / 50000000000000000000), D3 := ((5668307232142857151 : Rat) / 200000000000000000000), D4 := ((25882104017857122939 : Rat) / 200000000000000000000), LB := ((6569785541643991 : Rat) / 100000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133565057232142857151 : Rat) / 50000000000000000000), R := ((538284671696428571597 : Rat) / 200000000000000000000), D0 := ((538284671696428571597 : Rat) / 200000000000000000000), D1 := ((174789651696428571597 : Rat) / 200000000000000000000), D2 := ((26697671696428571597 : Rat) / 200000000000000000000), D3 := ((4024442767857142993 : Rat) / 200000000000000000000), D4 := ((5053449196428566447 : Rat) / 50000000000000000000), LB := ((2244198137350959 : Rat) / 20000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((538284671696428571597 : Rat) / 200000000000000000000), R := ((54230911446428571459 : Rat) / 20000000000000000000), D0 := ((54230911446428571459 : Rat) / 20000000000000000000), D1 := ((17881409446428571459 : Rat) / 20000000000000000000), D2 := ((3072211446428571459 : Rat) / 20000000000000000000), D3 := ((4024442767857142993 : Rat) / 100000000000000000000), D4 := ((3237870803571424559 : Rat) / 40000000000000000000), LB := ((6853075890644877 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((54230911446428571459 : Rat) / 20000000000000000000), R := ((2173260900625000001353 : Rat) / 800000000000000000000), D0 := ((2173260900625000001353 : Rat) / 800000000000000000000), D1 := ((719280820625000001353 : Rat) / 800000000000000000000), D2 := ((126912900625000001353 : Rat) / 800000000000000000000), D3 := ((36219984910714286937 : Rat) / 800000000000000000000), D4 := ((6082455624999989901 : Rat) / 100000000000000000000), LB := ((2040127716622331 : Rat) / 100000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2173260900625000001353 : Rat) / 800000000000000000000), R := ((1088642671696428572173 : Rat) / 400000000000000000000), D0 := ((1088642671696428572173 : Rat) / 400000000000000000000), D1 := ((361652631696428572173 : Rat) / 400000000000000000000), D2 := ((65468671696428572173 : Rat) / 400000000000000000000), D3 := ((4024442767857142993 : Rat) / 80000000000000000000), D4 := ((8927040446428555243 : Rat) / 160000000000000000000), LB := ((2109307930975829 : Rat) / 250000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1088642671696428572173 : Rat) / 400000000000000000000), R := ((871719025910714286337 : Rat) / 320000000000000000000), D0 := ((871719025910714286337 : Rat) / 320000000000000000000), D1 := ((290126993910714286337 : Rat) / 320000000000000000000), D2 := ((53179825910714286337 : Rat) / 320000000000000000000), D3 := ((84513298125000002853 : Rat) / 1600000000000000000000), D4 := ((20305379732142816611 : Rat) / 400000000000000000000), LB := ((10096407246006023 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((871719025910714286337 : Rat) / 320000000000000000000), R := ((2181309786160714287339 : Rat) / 800000000000000000000), D0 := ((2181309786160714287339 : Rat) / 800000000000000000000), D1 := ((727329706160714287339 : Rat) / 800000000000000000000), D2 := ((134961786160714287339 : Rat) / 800000000000000000000), D3 := ((44268870446428572923 : Rat) / 800000000000000000000), D4 := ((77197076160714123451 : Rat) / 1600000000000000000000), LB := ((1526558574152237 : Rat) / 250000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2181309786160714287339 : Rat) / 800000000000000000000), R := ((4366644015089285717671 : Rat) / 1600000000000000000000), D0 := ((4366644015089285717671 : Rat) / 1600000000000000000000), D1 := ((1458683855089285717671 : Rat) / 1600000000000000000000), D2 := ((273948015089285717671 : Rat) / 1600000000000000000000), D3 := ((92562183660714288839 : Rat) / 1600000000000000000000), D4 := ((36586316696428490229 : Rat) / 800000000000000000000), LB := ((3510013865078293 : Rat) / 1250000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4366644015089285717671 : Rat) / 1600000000000000000000), R := ((546333557232142857583 : Rat) / 200000000000000000000), D0 := ((546333557232142857583 : Rat) / 200000000000000000000), D1 := ((182838537232142857583 : Rat) / 200000000000000000000), D2 := ((34746557232142857583 : Rat) / 200000000000000000000), D3 := ((12073328303571428979 : Rat) / 200000000000000000000), D4 := ((13829638124999967493 : Rat) / 320000000000000000000), LB := ((21817742658664097 : Rat) / 100000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546333557232142857583 : Rat) / 200000000000000000000), R := ((8745361358482142864321 : Rat) / 3200000000000000000000), D0 := ((8745361358482142864321 : Rat) / 3200000000000000000000), D1 := ((2929441038482142864321 : Rat) / 3200000000000000000000), D2 := ((559969358482142864321 : Rat) / 3200000000000000000000), D3 := ((197197695625000006657 : Rat) / 3200000000000000000000), D4 := ((8140468482142836809 : Rat) / 200000000000000000000), LB := ((135035026534851 : Rat) / 40000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8745361358482142864321 : Rat) / 3200000000000000000000), R := ((4374692900625000003657 : Rat) / 1600000000000000000000), D0 := ((4374692900625000003657 : Rat) / 1600000000000000000000), D1 := ((1466732740625000003657 : Rat) / 1600000000000000000000), D2 := ((281996900625000003657 : Rat) / 1600000000000000000000), D3 := ((4024442767857142993 : Rat) / 64000000000000000000), D4 := ((126223052946428245951 : Rat) / 3200000000000000000000), LB := ((1069609661559201 : Rat) / 400000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4374692900625000003657 : Rat) / 1600000000000000000000), R := ((8753410244017857150307 : Rat) / 3200000000000000000000), D0 := ((8753410244017857150307 : Rat) / 3200000000000000000000), D1 := ((2937489924017857150307 : Rat) / 3200000000000000000000), D2 := ((568018244017857150307 : Rat) / 3200000000000000000000), D3 := ((205246581160714292643 : Rat) / 3200000000000000000000), D4 := ((61099305089285551479 : Rat) / 1600000000000000000000), LB := ((21741989660769567 : Rat) / 10000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8753410244017857150307 : Rat) / 3200000000000000000000), R := ((87574346867857142933 : Rat) / 32000000000000000000), D0 := ((87574346867857142933 : Rat) / 32000000000000000000), D1 := ((29415143667857142933 : Rat) / 32000000000000000000), D2 := ((5720426867857142933 : Rat) / 32000000000000000000), D3 := ((52317755982142858909 : Rat) / 800000000000000000000), D4 := ((23634833482142791993 : Rat) / 640000000000000000000), LB := ((18834659754177197 : Rat) / 10000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87574346867857142933 : Rat) / 32000000000000000000), R := ((8761459129553571436293 : Rat) / 3200000000000000000000), D0 := ((8761459129553571436293 : Rat) / 3200000000000000000000), D1 := ((2945538809553571436293 : Rat) / 3200000000000000000000), D2 := ((576067129553571436293 : Rat) / 3200000000000000000000), D3 := ((213295466696428578629 : Rat) / 3200000000000000000000), D4 := ((28537431160714204243 : Rat) / 800000000000000000000), LB := ((18099932847711053 : Rat) / 10000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8761459129553571436293 : Rat) / 3200000000000000000000), R := ((4382741786160714289643 : Rat) / 1600000000000000000000), D0 := ((4382741786160714289643 : Rat) / 1600000000000000000000), D1 := ((1474781626160714289643 : Rat) / 1600000000000000000000), D2 := ((290045786160714289643 : Rat) / 1600000000000000000000), D3 := ((108659954732142860811 : Rat) / 1600000000000000000000), D4 := ((110125281874999673979 : Rat) / 3200000000000000000000), LB := ((122698831597403 : Rat) / 62500000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4382741786160714289643 : Rat) / 1600000000000000000000), R := ((8769508015089285722279 : Rat) / 3200000000000000000000), D0 := ((8769508015089285722279 : Rat) / 3200000000000000000000), D1 := ((2953587695089285722279 : Rat) / 3200000000000000000000), D2 := ((584116015089285722279 : Rat) / 3200000000000000000000), D3 := ((44268870446428572923 : Rat) / 640000000000000000000), D4 := ((53050419553571265493 : Rat) / 1600000000000000000000), LB := ((23538197441803077 : Rat) / 10000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8769508015089285722279 : Rat) / 3200000000000000000000), R := ((1096691557232142858159 : Rat) / 400000000000000000000), D0 := ((1096691557232142858159 : Rat) / 400000000000000000000), D1 := ((369701517232142858159 : Rat) / 400000000000000000000), D2 := ((73517557232142858159 : Rat) / 400000000000000000000), D3 := ((28171099375000000951 : Rat) / 400000000000000000000), D4 := ((102076396339285387993 : Rat) / 3200000000000000000000), LB := ((1497138719494917 : Rat) / 500000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1096691557232142858159 : Rat) / 400000000000000000000), R := ((1755511380125000001653 : Rat) / 640000000000000000000), D0 := ((1755511380125000001653 : Rat) / 640000000000000000000), D1 := ((592327316125000001653 : Rat) / 640000000000000000000), D2 := ((118432980125000001653 : Rat) / 640000000000000000000), D3 := ((229393237767857150601 : Rat) / 3200000000000000000000), D4 := ((19610390714285649 : Rat) / 640000000000000000), LB := ((3898732706905217 : Rat) / 1000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1755511380125000001653 : Rat) / 640000000000000000000), R := ((4390790671696428575629 : Rat) / 1600000000000000000000), D0 := ((4390790671696428575629 : Rat) / 1600000000000000000000), D1 := ((1482830511696428575629 : Rat) / 1600000000000000000000), D2 := ((298094671696428575629 : Rat) / 1600000000000000000000), D3 := ((116708840267857146797 : Rat) / 1600000000000000000000), D4 := ((94027510803571102007 : Rat) / 3200000000000000000000), LB := ((79428970958491 : Rat) / 15625000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4390790671696428575629 : Rat) / 1600000000000000000000), R := ((2197407557232142859311 : Rat) / 800000000000000000000), D0 := ((2197407557232142859311 : Rat) / 800000000000000000000), D1 := ((743427477232142859311 : Rat) / 800000000000000000000), D2 := ((151059557232142859311 : Rat) / 800000000000000000000), D3 := ((12073328303571428979 : Rat) / 160000000000000000000), D4 := ((45001534017856979507 : Rat) / 1600000000000000000000), LB := ((522345564131263 : Rat) / 250000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2197407557232142859311 : Rat) / 800000000000000000000), R := ((879767911446428572323 : Rat) / 320000000000000000000), D0 := ((879767911446428572323 : Rat) / 320000000000000000000), D1 := ((298175879446428572323 : Rat) / 320000000000000000000), D2 := ((61228711446428572323 : Rat) / 320000000000000000000), D3 := ((124757725803571432783 : Rat) / 1600000000000000000000), D4 := ((20488545624999918257 : Rat) / 800000000000000000000), LB := ((12261057177673007 : Rat) / 2000000000000000000) },
  { w1 := ((374459166683371 : Rat) / 400000000000000), w2 := ((1185354027442389 : Rat) / 25000000000000000), w3 := ((7244425675038617 : Rat) / 50000000000000000), w4 := ((6866303031122961 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133565057232142857151 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((879767911446428572323 : Rat) / 320000000000000000000), R := ((8599343750000000009 : Rat) / 3125000000000000000), D0 := ((8599343750000000009 : Rat) / 3125000000000000000), D1 := ((2919734062500000009 : Rat) / 3125000000000000000), D2 := ((605796875000000009 : Rat) / 3125000000000000000), D3 := ((4024442767857142993 : Rat) / 50000000000000000000), D4 := ((36952648482142693521 : Rat) / 1600000000000000000000), LB := ((5834695368830023 : Rat) / 500000000000000000) }
]

def block336RightChunk000L : Rat := ((87579725446428571573 : Rat) / 50000000000000000000)
def block336RightChunk000R : Rat := ((8599343750000000009 : Rat) / 3125000000000000000)

def block336RightChunk000Certificate : Bool :=
  allBoxesValid block336RightChunk000 &&
  coversFromBool block336RightChunk000 block336RightChunk000L block336RightChunk000R

theorem block336RightChunk000Certificate_eq_true :
    block336RightChunk000Certificate = true := by
  native_decide

def block336RightChainCertificate : Bool :=
  decide (
    block336RightL = ((87579725446428571573 : Rat) / 50000000000000000000) /\
    ((8599343750000000009 : Rat) / 3125000000000000000) = block336RightR)

theorem block336RightChainCertificate_eq_true :
    block336RightChainCertificate = true := by
  native_decide

def block336LeftBoxCount : Nat := boxCount block336LeftBoxes
def block336RightBoxCount : Nat := 62

def block336_rational_certificate : Prop :=
    block336LeftCertificate = true /\
    block336RightChainCertificate = true /\
    block336RightChunk000Certificate = true

theorem block336_rational_certificate_proof :
    block336_rational_certificate := by
  exact ⟨block336LeftCertificate_eq_true, block336RightChainCertificate_eq_true, block336RightChunk000Certificate_eq_true⟩

end Block336
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block336

open Set

def block336W1 : Rat := ((374459166683371 : Rat) / 400000000000000)
def block336W2 : Rat := ((1185354027442389 : Rat) / 25000000000000000)
def block336W3 : Rat := ((7244425675038617 : Rat) / 50000000000000000)
def block336W4 : Rat := ((6866303031122961 : Rat) / 50000000000000000)
def block336S1 : Rat := ((18174751 : Rat) / 10000000)
def block336S2 : Rat := ((511587 : Rat) / 200000)
def block336S3 : Rat := ((133565057232142857151 : Rat) / 50000000000000000000)
def block336S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block336V (y : ℝ) : ℝ :=
  ratPotential block336W1 block336W2 block336W3 block336W4 block336S1 block336S2 block336S3 block336S4 y

def block336LeftParamsCertificate : Bool :=
  allBoxesSameParams block336LeftBoxes block336W1 block336W2 block336W3 block336W4 block336S1 block336S2 block336S3 block336S4

theorem block336LeftParamsCertificate_eq_true :
    block336LeftParamsCertificate = true := by
  native_decide

theorem block336_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block336LeftL : ℝ) (block336LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block336S1 : ℝ))
    (hy2ne : y ≠ (block336S2 : ℝ))
    (hy3ne : y ≠ (block336S3 : ℝ))
    (hy4ne : y ≠ (block336S4 : ℝ)) :
    0 < block336V y := by
  have hcert := block336LeftCertificate_eq_true
  unfold block336LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block336LeftBoxes) (lo := block336LeftL) (hi := block336LeftR)
    (w1 := block336W1) (w2 := block336W2) (w3 := block336W3) (w4 := block336W4)
    (s1 := block336S1) (s2 := block336S2) (s3 := block336S3) (s4 := block336S4)
    hboxes hcover block336LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block336RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block336RightChunk000 block336W1 block336W2 block336W3 block336W4 block336S1 block336S2 block336S3 block336S4

theorem block336RightChunk000ParamsCertificate_eq_true :
    block336RightChunk000ParamsCertificate = true := by
  native_decide

theorem block336_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block336RightChunk000L : ℝ) (block336RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block336S1 : ℝ))
    (hy2ne : y ≠ (block336S2 : ℝ))
    (hy3ne : y ≠ (block336S3 : ℝ))
    (hy4ne : y ≠ (block336S4 : ℝ)) :
    0 < block336V y := by
  have hcert := block336RightChunk000Certificate_eq_true
  unfold block336RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block336RightChunk000) (lo := block336RightChunk000L) (hi := block336RightChunk000R)
    (w1 := block336W1) (w2 := block336W2) (w3 := block336W3) (w4 := block336W4)
    (s1 := block336S1) (s2 := block336S2) (s3 := block336S3) (s4 := block336S4)
    hboxes hcover block336RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block336_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block336RightL : ℝ) (block336RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block336S1 : ℝ))
    (hy2ne : y ≠ (block336S2 : ℝ))
    (hy3ne : y ≠ (block336S3 : ℝ))
    (hy4ne : y ≠ (block336S4 : ℝ)) :
    0 < block336V y := by
  have hL : (block336RightChunk000L : ℝ) = (block336RightL : ℝ) := by
    norm_num [block336RightChunk000L, block336RightL]
  have hR : (block336RightChunk000R : ℝ) = (block336RightR : ℝ) := by
    norm_num [block336RightChunk000R, block336RightR]
  have hyc : y ∈ Icc (block336RightChunk000L : ℝ) (block336RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block336_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block336_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block336LeftL : ℝ) (block336LeftR : ℝ) →
    y ≠ 0 → y ≠ (block336S1 : ℝ) → y ≠ (block336S2 : ℝ) →
    y ≠ (block336S3 : ℝ) → y ≠ (block336S4 : ℝ) → 0 < block336V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block336RightL : ℝ) (block336RightR : ℝ) →
    y ≠ 0 → y ≠ (block336S1 : ℝ) → y ≠ (block336S2 : ℝ) →
    y ≠ (block336S3 : ℝ) → y ≠ (block336S4 : ℝ) → 0 < block336V y)

theorem block336_reallog_certificate_proof :
    block336_reallog_certificate := by
  exact ⟨block336_left_V_pos, block336_right_V_pos⟩

end Block336
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block336.block336V
#check Erdos1038Lean.M1817475.Block336.block336_left_V_pos
#check Erdos1038Lean.M1817475.Block336.block336_right_V_pos
#check Erdos1038Lean.M1817475.Block336.block336_reallog_certificate_proof
