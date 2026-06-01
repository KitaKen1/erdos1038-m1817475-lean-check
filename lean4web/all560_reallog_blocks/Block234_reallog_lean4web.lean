/-
Self-contained Lean4Web paste file.
Block 234 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block234

def block234LeftL : Rat := ((7715345982142857163 : Rat) / 10000000000000000000)
def block234LeftR : Rat := ((19293252232142857193 : Rat) / 25000000000000000000)
def block234RightL : Rat := ((17715345982142857163 : Rat) / 10000000000000000000)
def block234RightR : Rat := ((69293252232142857193 : Rat) / 25000000000000000000)

def block234LeftBoxes : List RatBox := [
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7715345982142857163 : Rat) / 10000000000000000000), R := ((19293252232142857193 : Rat) / 25000000000000000000), D0 := ((19293252232142857193 : Rat) / 25000000000000000000), D1 := ((10459405017857142837 : Rat) / 10000000000000000000), D2 := ((17864004017857142837 : Rat) / 10000000000000000000), D3 := ((9747106392857142837 : Rat) / 5000000000000000000), D4 := ((20129559767857141837 : Rat) / 10000000000000000000), LB := ((7344141192312803 : Rat) / 10000000000000000000) }
]

def block234LeftCertificate : Bool :=
  allBoxesValid block234LeftBoxes &&
  coversFromBool block234LeftBoxes block234LeftL block234LeftR

theorem block234LeftCertificate_eq_true :
    block234LeftCertificate = true := by
  native_decide

def block234RightChunk000 : List RatBox := [
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17715345982142857163 : Rat) / 10000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((459405017857142837 : Rat) / 10000000000000000000), D2 := ((7864004017857142837 : Rat) / 10000000000000000000), D3 := ((4747106392857142837 : Rat) / 5000000000000000000), D4 := ((10129559767857141837 : Rat) / 10000000000000000000), LB := ((5232550243281311 : Rat) / 2500000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((3805767523519 : Rat) / 31250000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((3785913520375417 : Rat) / 50000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((4406933392857142837 : Rat) / 10000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((2749881921732201 : Rat) / 62500000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3944145955357142837 : Rat) / 10000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((37974817476572977 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((3712752236607142837 : Rat) / 10000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((7451116169924339 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((1767455400942433 : Rat) / 100000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((3365661658482142837 : Rat) / 10000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((4477411966558459 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((3249964799107142837 : Rat) / 10000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((500816128278031 : Rat) / 400000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((3134267939732142837 : Rat) / 10000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((5370202875417757 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((3076419510044642837 : Rat) / 10000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((23997179701049087 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((3018571080357142837 : Rat) / 10000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((2524400496381203 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((2989646865513392837 : Rat) / 10000000000000000000), D4 := ((3624993847656249 : Rat) / 10000000000000000), LB := ((38102929586809747 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((2960722650669642837 : Rat) / 10000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((1326158958102723 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((2931798435825892837 : Rat) / 10000000000000000000), D4 := ((3567145417968749 : Rat) / 10000000000000000), LB := ((3941910506158261 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2902874220982142837 : Rat) / 10000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((58564710526883 : Rat) / 100000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((2873950006138392837 : Rat) / 10000000000000000000), D4 := ((3509296988281249 : Rat) / 10000000000000000), LB := ((22961558577430097 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((2859487898716517837 : Rat) / 10000000000000000000), D4 := ((1747417440429687 : Rat) / 5000000000000000), LB := ((9360035826266669 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2845025791294642837 : Rat) / 10000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((14704041926697081 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((2830563683872767837 : Rat) / 10000000000000000000), D4 := ((433238833251953 : Rat) / 1250000000000000), LB := ((10916602227515199 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((2816101576450892837 : Rat) / 10000000000000000000), D4 := ((3451448558593749 : Rat) / 10000000000000000), LB := ((7360996627556043 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((2801639469029017837 : Rat) / 10000000000000000000), D4 := ((1718493225585937 : Rat) / 5000000000000000), LB := ((20202927832154577 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2787177361607142837 : Rat) / 10000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((119856410725587 : Rat) / 1250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((25030732357 : Rat) / 10240000000), D0 := ((25030732357 : Rat) / 10240000000), D1 := ((6419787333 : Rat) / 10240000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((2772715254185267837 : Rat) / 10000000000000000000), D4 := ((852015559082031 : Rat) / 2500000000000000), LB := ((5518989634164459 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25030732357 : Rat) / 10240000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((1162522043 : Rat) / 10240000000), D3 := ((2765484200474330337 : Rat) / 10000000000000000000), D4 := ((6801662365234373 : Rat) / 20000000000000000), LB := ((9697933788357649 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((5009108311 : Rat) / 2048000000), D0 := ((5009108311 : Rat) / 2048000000), D1 := ((6434596531 : Rat) / 10240000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((2758253146763392837 : Rat) / 10000000000000000000), D4 := ((3393600128906249 : Rat) / 10000000000000000), LB := ((4209950736206239 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5009108311 : Rat) / 2048000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((229542569 : Rat) / 2048000000), D3 := ((2751022093052455337 : Rat) / 10000000000000000000), D4 := ((6772738150390623 : Rat) / 20000000000000000), LB := ((225136629092397 : Rat) / 312500000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((25060350753 : Rat) / 10240000000), D0 := ((25060350753 : Rat) / 10240000000), D1 := ((6449405729 : Rat) / 10240000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((2743791039341517837 : Rat) / 10000000000000000000), D4 := ((1689569010742187 : Rat) / 5000000000000000), LB := ((6051844769559139 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25060350753 : Rat) / 10240000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((1132903647 : Rat) / 10240000000), D3 := ((2736559985630580337 : Rat) / 10000000000000000000), D4 := ((6743813935546873 : Rat) / 20000000000000000), LB := ((310176738511983 : Rat) / 625000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((25075159951 : Rat) / 10240000000), D0 := ((25075159951 : Rat) / 10240000000), D1 := ((6464214927 : Rat) / 10240000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2729328931919642837 : Rat) / 10000000000000000000), D4 := ((3364675914062499 : Rat) / 10000000000000000), LB := ((39378393558905933 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25075159951 : Rat) / 10240000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((1118094449 : Rat) / 10240000000), D3 := ((2722097878208705337 : Rat) / 10000000000000000000), D4 := ((6714889720703123 : Rat) / 20000000000000000), LB := ((46521990203273 : Rat) / 156250000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((501651291 : Rat) / 204800000), R := ((25089969149 : Rat) / 10240000000), D0 := ((25089969149 : Rat) / 10240000000), D1 := ((51832193 : Rat) / 81920000), D2 := ((22213797 : Rat) / 204800000), D3 := ((2714866824497767837 : Rat) / 10000000000000000000), D4 := ((209388362915039 : Rat) / 625000000000000), LB := ((2082070001429709 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25089969149 : Rat) / 10240000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((1103285251 : Rat) / 10240000000), D3 := ((2707635770786830337 : Rat) / 10000000000000000000), D4 := ((6685965505859373 : Rat) / 20000000000000000), LB := ((391367432200267 : Rat) / 3125000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((25104778347 : Rat) / 10240000000), D0 := ((25104778347 : Rat) / 10240000000), D1 := ((6493833323 : Rat) / 10240000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((2700404717075892837 : Rat) / 10000000000000000000), D4 := ((3335751699218749 : Rat) / 10000000000000000), LB := ((4888839348018981 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25104778347 : Rat) / 10240000000), R := ((50216961293 : Rat) / 20480000000), D0 := ((50216961293 : Rat) / 20480000000), D1 := ((2599014249 : Rat) / 4096000000), D2 := ((1088476053 : Rat) / 10240000000), D3 := ((2693173663364955337 : Rat) / 10000000000000000000), D4 := ((6657041291015623 : Rat) / 20000000000000000), LB := ((1547205736293529 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50216961293 : Rat) / 20480000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((2169547507 : Rat) / 20480000000), D3 := ((2689558136509486587 : Rat) / 10000000000000000000), D4 := ((13299620474609371 : Rat) / 40000000000000000), LB := ((5862664573269977 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((50231770491 : Rat) / 20480000000), D0 := ((50231770491 : Rat) / 20480000000), D1 := ((13009880443 : Rat) / 20480000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((2685942609654017837 : Rat) / 10000000000000000000), D4 := ((1660644795898437 : Rat) / 5000000000000000), LB := ((5553421509380541 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50231770491 : Rat) / 20480000000), R := ((5023917509 : Rat) / 2048000000), D0 := ((5023917509 : Rat) / 2048000000), D1 := ((6508642521 : Rat) / 10240000000), D2 := ((2154738309 : Rat) / 20480000000), D3 := ((2682327082798549087 : Rat) / 10000000000000000000), D4 := ((13270696259765621 : Rat) / 40000000000000000), LB := ((5261168227641139 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5023917509 : Rat) / 2048000000), R := ((50246579689 : Rat) / 20480000000), D0 := ((50246579689 : Rat) / 20480000000), D1 := ((13024689641 : Rat) / 20480000000), D2 := ((214733371 : Rat) / 2048000000), D3 := ((2678711555943080337 : Rat) / 10000000000000000000), D4 := ((6628117076171873 : Rat) / 20000000000000000), LB := ((4985979941887903 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50246579689 : Rat) / 20480000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((2139929111 : Rat) / 20480000000), D3 := ((2675096029087611587 : Rat) / 10000000000000000000), D4 := ((13241772044921871 : Rat) / 40000000000000000), LB := ((9455865230844629 : Rat) / 20000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((50261388887 : Rat) / 20480000000), D0 := ((50261388887 : Rat) / 20480000000), D1 := ((13039498839 : Rat) / 20480000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2671480502232142837 : Rat) / 10000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((2243551485481901 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50261388887 : Rat) / 20480000000), R := ((25134396743 : Rat) / 10240000000), D0 := ((25134396743 : Rat) / 10240000000), D1 := ((6523451719 : Rat) / 10240000000), D2 := ((2125119913 : Rat) / 20480000000), D3 := ((2667864975376674087 : Rat) / 10000000000000000000), D4 := ((13212847830078121 : Rat) / 40000000000000000), LB := ((2131784250383323 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25134396743 : Rat) / 10240000000), R := ((10055239617 : Rat) / 4096000000), D0 := ((10055239617 : Rat) / 4096000000), D1 := ((13054308037 : Rat) / 20480000000), D2 := ((1058857657 : Rat) / 10240000000), D3 := ((2664249448521205337 : Rat) / 10000000000000000000), D4 := ((6599192861328123 : Rat) / 20000000000000000), LB := ((40574074768885693 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((10055239617 : Rat) / 4096000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((422062143 : Rat) / 4096000000), D3 := ((2660633921665736587 : Rat) / 10000000000000000000), D4 := ((13183923615234371 : Rat) / 40000000000000000), LB := ((967174740419581 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((50291007283 : Rat) / 20480000000), D0 := ((50291007283 : Rat) / 20480000000), D1 := ((2613823447 : Rat) / 4096000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((2657018394810267837 : Rat) / 10000000000000000000), D4 := ((823091344238281 : Rat) / 2500000000000000), LB := ((36975228184063513 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50291007283 : Rat) / 20480000000), R := ((25149205941 : Rat) / 10240000000), D0 := ((25149205941 : Rat) / 10240000000), D1 := ((6538260917 : Rat) / 10240000000), D2 := ((2095501517 : Rat) / 20480000000), D3 := ((2653402867954799087 : Rat) / 10000000000000000000), D4 := ((13154999400390621 : Rat) / 40000000000000000), LB := ((3543959722111939 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25149205941 : Rat) / 10240000000), R := ((50305816481 : Rat) / 20480000000), D0 := ((50305816481 : Rat) / 20480000000), D1 := ((13083926433 : Rat) / 20480000000), D2 := ((1044048459 : Rat) / 10240000000), D3 := ((2649787341099330337 : Rat) / 10000000000000000000), D4 := ((6570268646484373 : Rat) / 20000000000000000), LB := ((17040455852999903 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50305816481 : Rat) / 20480000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((2080692319 : Rat) / 20480000000), D3 := ((2646171814243861587 : Rat) / 10000000000000000000), D4 := ((13126075185546871 : Rat) / 40000000000000000), LB := ((32899994956861467 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((50320625679 : Rat) / 20480000000), D0 := ((50320625679 : Rat) / 20480000000), D1 := ((13098735631 : Rat) / 20480000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((2642556287388392837 : Rat) / 10000000000000000000), D4 := ((3277903269531249 : Rat) / 10000000000000000), LB := ((318976787459041 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50320625679 : Rat) / 20480000000), R := ((25164015139 : Rat) / 10240000000), D0 := ((25164015139 : Rat) / 10240000000), D1 := ((1310614023 : Rat) / 2048000000), D2 := ((2065883121 : Rat) / 20480000000), D3 := ((2638940760532924087 : Rat) / 10000000000000000000), D4 := ((13097150970703121 : Rat) / 40000000000000000), LB := ((1553740170778667 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25164015139 : Rat) / 10240000000), R := ((50335434877 : Rat) / 20480000000), D0 := ((50335434877 : Rat) / 20480000000), D1 := ((13113544829 : Rat) / 20480000000), D2 := ((1029239261 : Rat) / 10240000000), D3 := ((2635325233677455337 : Rat) / 10000000000000000000), D4 := ((6541344431640623 : Rat) / 20000000000000000), LB := ((6086443599340463 : Rat) / 20000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50335434877 : Rat) / 20480000000), R := ((12585709869 : Rat) / 5120000000), D0 := ((12585709869 : Rat) / 5120000000), D1 := ((3280237357 : Rat) / 5120000000), D2 := ((2051073923 : Rat) / 20480000000), D3 := ((2631709706821986587 : Rat) / 10000000000000000000), D4 := ((13068226755859371 : Rat) / 40000000000000000), LB := ((29970780329019453 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12585709869 : Rat) / 5120000000), R := ((2014009763 : Rat) / 819200000), D0 := ((2014009763 : Rat) / 819200000), D1 := ((13128354027 : Rat) / 20480000000), D2 := ((510917331 : Rat) / 5120000000), D3 := ((2628094179966517837 : Rat) / 10000000000000000000), D4 := ((1631720581054687 : Rat) / 5000000000000000), LB := ((2969135718321747 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2014009763 : Rat) / 819200000), R := ((25178824337 : Rat) / 10240000000), D0 := ((25178824337 : Rat) / 10240000000), D1 := ((6567879313 : Rat) / 10240000000), D2 := ((81450589 : Rat) / 819200000), D3 := ((2624478653111049087 : Rat) / 10000000000000000000), D4 := ((13039302541015621 : Rat) / 40000000000000000), LB := ((2959482438635447 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25178824337 : Rat) / 10240000000), R := ((50365053273 : Rat) / 20480000000), D0 := ((50365053273 : Rat) / 20480000000), D1 := ((525726529 : Rat) / 819200000), D2 := ((1014430063 : Rat) / 10240000000), D3 := ((2620863126255580337 : Rat) / 10000000000000000000), D4 := ((6512420216796873 : Rat) / 20000000000000000), LB := ((1484103347386273 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50365053273 : Rat) / 20480000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((2021455527 : Rat) / 20480000000), D3 := ((2617247599400111587 : Rat) / 10000000000000000000), D4 := ((13010378326171871 : Rat) / 40000000000000000), LB := ((1497698959452773 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((50379862471 : Rat) / 20480000000), D0 := ((50379862471 : Rat) / 20480000000), D1 := ((13157972423 : Rat) / 20480000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2613632072544642837 : Rat) / 10000000000000000000), D4 := ((3248979054687499 : Rat) / 10000000000000000), LB := ((380143310942261 : Rat) / 1250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50379862471 : Rat) / 20480000000), R := ((5038726707 : Rat) / 2048000000), D0 := ((5038726707 : Rat) / 2048000000), D1 := ((6582688511 : Rat) / 10240000000), D2 := ((2006646329 : Rat) / 20480000000), D3 := ((2610016545689174087 : Rat) / 10000000000000000000), D4 := ((12981454111328121 : Rat) / 40000000000000000), LB := ((6211087469861487 : Rat) / 20000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5038726707 : Rat) / 2048000000), R := ((50394671669 : Rat) / 20480000000), D0 := ((50394671669 : Rat) / 20480000000), D1 := ((13172781621 : Rat) / 20480000000), D2 := ((199924173 : Rat) / 2048000000), D3 := ((2606401018833705337 : Rat) / 10000000000000000000), D4 := ((6483496001953123 : Rat) / 20000000000000000), LB := ((1594340983364917 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50394671669 : Rat) / 20480000000), R := ((12600519067 : Rat) / 5120000000), D0 := ((12600519067 : Rat) / 5120000000), D1 := ((659009311 : Rat) / 1024000000), D2 := ((1991837131 : Rat) / 20480000000), D3 := ((2602785491978236587 : Rat) / 10000000000000000000), D4 := ((12952529896484371 : Rat) / 40000000000000000), LB := ((8226636184635941 : Rat) / 25000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12600519067 : Rat) / 5120000000), R := ((50409480867 : Rat) / 20480000000), D0 := ((50409480867 : Rat) / 20480000000), D1 := ((13187590819 : Rat) / 20480000000), D2 := ((496108133 : Rat) / 5120000000), D3 := ((2599169965122767837 : Rat) / 10000000000000000000), D4 := ((404314618408203 : Rat) / 1250000000000000), LB := ((34115555466691927 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50409480867 : Rat) / 20480000000), R := ((25208442733 : Rat) / 10240000000), D0 := ((25208442733 : Rat) / 10240000000), D1 := ((6597497709 : Rat) / 10240000000), D2 := ((1977027933 : Rat) / 20480000000), D3 := ((2595554438267299087 : Rat) / 10000000000000000000), D4 := ((12923605681640621 : Rat) / 40000000000000000), LB := ((710296097868629 : Rat) / 2000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25208442733 : Rat) / 10240000000), R := ((10084858013 : Rat) / 4096000000), D0 := ((10084858013 : Rat) / 4096000000), D1 := ((13202400017 : Rat) / 20480000000), D2 := ((984811667 : Rat) / 10240000000), D3 := ((2591938911411830337 : Rat) / 10000000000000000000), D4 := ((6454571787109373 : Rat) / 20000000000000000), LB := ((231907852159801 : Rat) / 625000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((10084858013 : Rat) / 4096000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((392443747 : Rat) / 4096000000), D3 := ((2588323384556361587 : Rat) / 10000000000000000000), D4 := ((12894681466796871 : Rat) / 40000000000000000), LB := ((3888788358459849 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((50439099263 : Rat) / 20480000000), D0 := ((50439099263 : Rat) / 20480000000), D1 := ((2643441843 : Rat) / 4096000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((2584707857700892837 : Rat) / 10000000000000000000), D4 := ((3220054839843749 : Rat) / 10000000000000000), LB := ((8172734191727593 : Rat) / 20000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50439099263 : Rat) / 20480000000), R := ((25223251931 : Rat) / 10240000000), D0 := ((25223251931 : Rat) / 10240000000), D1 := ((6612306907 : Rat) / 10240000000), D2 := ((1947409537 : Rat) / 20480000000), D3 := ((2581092330845424087 : Rat) / 10000000000000000000), D4 := ((12865757251953121 : Rat) / 40000000000000000), LB := ((43033613557955097 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25223251931 : Rat) / 10240000000), R := ((50453908461 : Rat) / 20480000000), D0 := ((50453908461 : Rat) / 20480000000), D1 := ((13232018413 : Rat) / 20480000000), D2 := ((970002469 : Rat) / 10240000000), D3 := ((2577476803989955337 : Rat) / 10000000000000000000), D4 := ((6425647572265623 : Rat) / 20000000000000000), LB := ((5674839671581007 : Rat) / 12500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50453908461 : Rat) / 20480000000), R := ((2523065653 : Rat) / 1024000000), D0 := ((2523065653 : Rat) / 1024000000), D1 := ((3309855753 : Rat) / 5120000000), D2 := ((1932600339 : Rat) / 20480000000), D3 := ((2573861277134486587 : Rat) / 10000000000000000000), D4 := ((12836833037109371 : Rat) / 40000000000000000), LB := ((4795999945405721 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2523065653 : Rat) / 1024000000), R := ((50468717659 : Rat) / 20480000000), D0 := ((50468717659 : Rat) / 20480000000), D1 := ((13246827611 : Rat) / 20480000000), D2 := ((96259787 : Rat) / 1024000000), D3 := ((2570245750279017837 : Rat) / 10000000000000000000), D4 := ((1602796366210937 : Rat) / 5000000000000000), LB := ((5071848807862017 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50468717659 : Rat) / 20480000000), R := ((25238061129 : Rat) / 10240000000), D0 := ((25238061129 : Rat) / 10240000000), D1 := ((1325423221 : Rat) / 2048000000), D2 := ((1917791141 : Rat) / 20480000000), D3 := ((2566630223423549087 : Rat) / 10000000000000000000), D4 := ((12807908822265621 : Rat) / 40000000000000000), LB := ((5367522291532117 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25238061129 : Rat) / 10240000000), R := ((50483526857 : Rat) / 20480000000), D0 := ((50483526857 : Rat) / 20480000000), D1 := ((13261636809 : Rat) / 20480000000), D2 := ((955193271 : Rat) / 10240000000), D3 := ((2563014696568080337 : Rat) / 10000000000000000000), D4 := ((6396723357421873 : Rat) / 20000000000000000), LB := ((568312551959757 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50483526857 : Rat) / 20480000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((1902981943 : Rat) / 20480000000), D3 := ((2559399169712611587 : Rat) / 10000000000000000000), D4 := ((12778984607421871 : Rat) / 40000000000000000), LB := ((3009382394457 : Rat) / 5000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((25252870327 : Rat) / 10240000000), D0 := ((25252870327 : Rat) / 10240000000), D1 := ((6641925303 : Rat) / 10240000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((903947181948861 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25252870327 : Rat) / 10240000000), R := ((12630137463 : Rat) / 5120000000), D0 := ((12630137463 : Rat) / 5120000000), D1 := ((3324664951 : Rat) / 5120000000), D2 := ((940384073 : Rat) / 10240000000), D3 := ((2548552589146205337 : Rat) / 10000000000000000000), D4 := ((6367799142578123 : Rat) / 20000000000000000), LB := ((434311722046013 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12630137463 : Rat) / 5120000000), R := ((1010707181 : Rat) / 409600000), D0 := ((1010707181 : Rat) / 409600000), D1 := ((6656734501 : Rat) / 10240000000), D2 := ((466489737 : Rat) / 5120000000), D3 := ((2541321535435267837 : Rat) / 10000000000000000000), D4 := ((794167129394531 : Rat) / 2500000000000000), LB := ((17287345399165377 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1010707181 : Rat) / 409600000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 81920000), D3 := ((2534090481724330337 : Rat) / 10000000000000000000), D4 := ((6338874927734373 : Rat) / 20000000000000000), LB := ((13358163642170767 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((25282488723 : Rat) / 10240000000), D0 := ((25282488723 : Rat) / 10240000000), D1 := ((6671543699 : Rat) / 10240000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((2526859428013392837 : Rat) / 10000000000000000000), D4 := ((3162206410156249 : Rat) / 10000000000000000), LB := ((36982436174565203 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25282488723 : Rat) / 10240000000), R := ((12644946661 : Rat) / 5120000000), D0 := ((12644946661 : Rat) / 5120000000), D1 := ((3339474149 : Rat) / 5120000000), D2 := ((910765677 : Rat) / 10240000000), D3 := ((2519628374302455337 : Rat) / 10000000000000000000), D4 := ((6309950712890623 : Rat) / 20000000000000000), LB := ((48095143557390363 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12644946661 : Rat) / 5120000000), R := ((25297297921 : Rat) / 10240000000), D0 := ((25297297921 : Rat) / 10240000000), D1 := ((6686352897 : Rat) / 10240000000), D2 := ((451680539 : Rat) / 5120000000), D3 := ((2512397320591517837 : Rat) / 10000000000000000000), D4 := ((1573872151367187 : Rat) / 5000000000000000), LB := ((93850223678259 : Rat) / 156250000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25297297921 : Rat) / 10240000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((895956479 : Rat) / 10240000000), D3 := ((2505166266880580337 : Rat) / 10000000000000000000), D4 := ((6281026498046873 : Rat) / 20000000000000000), LB := ((364496790113987 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((632617563 : Rat) / 256000000), R := ((25312107119 : Rat) / 10240000000), D0 := ((25312107119 : Rat) / 10240000000), D1 := ((1340232419 : Rat) / 2048000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((2497935213169642837 : Rat) / 10000000000000000000), D4 := ((3133282195312499 : Rat) / 10000000000000000), LB := ((1732218959069387 : Rat) / 2000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25312107119 : Rat) / 10240000000), R := ((12659755859 : Rat) / 5120000000), D0 := ((12659755859 : Rat) / 5120000000), D1 := ((3354283347 : Rat) / 5120000000), D2 := ((881147281 : Rat) / 10240000000), D3 := ((2490704159458705337 : Rat) / 10000000000000000000), D4 := ((6252102283203123 : Rat) / 20000000000000000), LB := ((1012093171704559 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12659755859 : Rat) / 5120000000), R := ((25326916317 : Rat) / 10240000000), D0 := ((25326916317 : Rat) / 10240000000), D1 := ((6715971293 : Rat) / 10240000000), D2 := ((436871341 : Rat) / 5120000000), D3 := ((2483473105747767837 : Rat) / 10000000000000000000), D4 := ((48731563873291 : Rat) / 156250000000000), LB := ((2334102447132419 : Rat) / 2000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25326916317 : Rat) / 10240000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((866338083 : Rat) / 10240000000), D3 := ((2476242052036830337 : Rat) / 10000000000000000000), D4 := ((6223178068359373 : Rat) / 20000000000000000), LB := ((831933006356627 : Rat) / 625000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((12674565057 : Rat) / 5120000000), D0 := ((12674565057 : Rat) / 5120000000), D1 := ((673818509 : Rat) / 1024000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((2469010998325892837 : Rat) / 10000000000000000000), D4 := ((3104357980468749 : Rat) / 10000000000000000), LB := ((1310498609345817 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12674565057 : Rat) / 5120000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((422062143 : Rat) / 5120000000), D3 := ((2454548890904017837 : Rat) / 10000000000000000000), D4 := ((1544947936523437 : Rat) / 5000000000000000), LB := ((638876688276141 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((2537874851 : Rat) / 1024000000), D0 := ((2537874851 : Rat) / 1024000000), D1 := ((3383901743 : Rat) / 5120000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((2440086783482142837 : Rat) / 10000000000000000000), D4 := ((3075433765624999 : Rat) / 10000000000000000), LB := ((10538398849620767 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2537874851 : Rat) / 1024000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((81450589 : Rat) / 1024000000), D3 := ((2425624676060267837 : Rat) / 10000000000000000000), D4 := ((765242914550781 : Rat) / 2500000000000000), LB := ((15079911762903991 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((12704183453 : Rat) / 5120000000), D0 := ((12704183453 : Rat) / 5120000000), D1 := ((3398710941 : Rat) / 5120000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((2411162568638392837 : Rat) / 10000000000000000000), D4 := ((3046509550781249 : Rat) / 10000000000000000), LB := ((2002385340375279 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12704183453 : Rat) / 5120000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((392443747 : Rat) / 5120000000), D3 := ((2396700461216517837 : Rat) / 10000000000000000000), D4 := ((1516023721679687 : Rat) / 5000000000000000), LB := ((2538133935966011 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((2382238353794642837 : Rat) / 10000000000000000000), D4 := ((3017585335937499 : Rat) / 10000000000000000), LB := ((6620364540060597 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((2353314138950892837 : Rat) / 10000000000000000000), D4 := ((2988661121093749 : Rat) / 10000000000000000), LB := ((9799741380272023 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((2324389924107142837 : Rat) / 10000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((8609274722958249 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((2295465709263392837 : Rat) / 10000000000000000000), D4 := ((2930812691406249 : Rat) / 10000000000000000), LB := ((256271866169111 : Rat) / 50000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((2266541494419642837 : Rat) / 10000000000000000000), D4 := ((2901888476562499 : Rat) / 10000000000000000), LB := ((547996378986379 : Rat) / 250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((2208693064732142837 : Rat) / 10000000000000000000), D4 := ((2844040046874999 : Rat) / 10000000000000000), LB := ((1677870026252467 : Rat) / 250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((2150844635044642837 : Rat) / 10000000000000000000), D4 := ((2786191617187499 : Rat) / 10000000000000000), LB := ((307364814762889 : Rat) / 25000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((9740094120766457 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1977299345982142837 : Rat) / 10000000000000000000), D4 := ((2612646328124999 : Rat) / 10000000000000000), LB := ((28657342264845703 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((4032302229265923 : Rat) / 100000000000000000) }
]

def block234RightChunk000L : Rat := ((17715345982142857163 : Rat) / 10000000000000000000)
def block234RightChunk000R : Rat := ((511587 : Rat) / 200000)

def block234RightChunk000Certificate : Bool :=
  allBoxesValid block234RightChunk000 &&
  coversFromBool block234RightChunk000 block234RightChunk000L block234RightChunk000R

theorem block234RightChunk000Certificate_eq_true :
    block234RightChunk000Certificate = true := by
  native_decide

def block234RightChunk001 : List RatBox := [
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((5061088631176129 : Rat) / 100000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((3210661233420681 : Rat) / 100000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((4880583137511593 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((5318931697700771 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((1985078269511907 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((6231270608336517 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((6080223879891 : Rat) / 1600000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((8330120679570091 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((34460242425181087 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((6472959576512491 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((4507580960830121 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((5434261134415197 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((2200206500926477 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((6716225103089285712211 : Rat) / 2560000000000000000000), D0 := ((6716225103089285712211 : Rat) / 2560000000000000000000), D1 := ((2063488847089285712211 : Rat) / 2560000000000000000000), D2 := ((167911503089285712211 : Rat) / 2560000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((1597805836895727 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6716225103089285712211 : Rat) / 2560000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((249421941482142854061 : Rat) / 2560000000000000000000), D4 := ((412070768910714031789 : Rat) / 2560000000000000000000), LB := ((1326188919978627 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((1343897104124999999577 : Rat) / 512000000000000000000), D0 := ((1343897104124999999577 : Rat) / 512000000000000000000), D1 := ((413349852924999999577 : Rat) / 512000000000000000000), D2 := ((34234384124999999577 : Rat) / 512000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((10718024980002627 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1343897104124999999577 : Rat) / 512000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((246161523946428568387 : Rat) / 2560000000000000000000), D4 := ((81762070274999949223 : Rat) / 512000000000000000000), LB := ((4173050028072889 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((3072905860493913 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((405549933839285460441 : Rat) / 2560000000000000000000), LB := ((20584596179468173 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((141202683940269 : Rat) / 625000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((2863317321162573 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((13456903337696428566977 : Rat) / 5120000000000000000000), D0 := ((13456903337696428566977 : Rat) / 5120000000000000000000), D1 := ((4151430825696428566977 : Rat) / 5120000000000000000000), D2 := ((360276137696428566977 : Rat) / 5120000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((7448709420111721 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13456903337696428566977 : Rat) / 5120000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((474390751446428565567 : Rat) / 5120000000000000000000), D4 := ((799688406303570921023 : Rat) / 5120000000000000000000), LB := ((3368286466627207 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((13460163755232142852651 : Rat) / 5120000000000000000000), D0 := ((13460163755232142852651 : Rat) / 5120000000000000000000), D1 := ((4154691243232142852651 : Rat) / 5120000000000000000000), D2 := ((363536555232142852651 : Rat) / 5120000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((606735335016817 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13460163755232142852651 : Rat) / 5120000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((471130333910714279893 : Rat) / 5120000000000000000000), D4 := ((796427988767856635349 : Rat) / 5120000000000000000000), LB := ((2720528819258883 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((538536966910714285533 : Rat) / 204800000000000000000), D0 := ((538536966910714285533 : Rat) / 204800000000000000000), D1 := ((166318066430714285533 : Rat) / 204800000000000000000), D2 := ((14671878910714285533 : Rat) / 204800000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((2428848209768547 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((538536966910714285533 : Rat) / 204800000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((467869916374999994219 : Rat) / 5120000000000000000000), D4 := ((31726702849285693987 : Rat) / 204800000000000000000), LB := ((2158641976983261 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((13466684590303571423999 : Rat) / 5120000000000000000000), D0 := ((13466684590303571423999 : Rat) / 5120000000000000000000), D1 := ((4161212078303571423999 : Rat) / 5120000000000000000000), D2 := ((370057390303571423999 : Rat) / 5120000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((19099190646074127 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13466684590303571423999 : Rat) / 5120000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((92921899767857141709 : Rat) / 1024000000000000000000), D4 := ((789907153696428064001 : Rat) / 5120000000000000000000), LB := ((1682690223827471 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((13469945007839285709673 : Rat) / 5120000000000000000000), D0 := ((13469945007839285709673 : Rat) / 5120000000000000000000), D1 := ((4164472495839285709673 : Rat) / 5120000000000000000000), D2 := ((373317807839285709673 : Rat) / 5120000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((115388125627319 : Rat) / 390625000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13469945007839285709673 : Rat) / 5120000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((461349081303571422871 : Rat) / 5120000000000000000000), D4 := ((786646736160713778327 : Rat) / 5120000000000000000000), LB := ((2585533536201279 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((13473205425374999995347 : Rat) / 5120000000000000000000), D0 := ((13473205425374999995347 : Rat) / 5120000000000000000000), D1 := ((4167732913374999995347 : Rat) / 5120000000000000000000), D2 := ((376578225374999995347 : Rat) / 5120000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((1130102648320419 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13473205425374999995347 : Rat) / 5120000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((458088663767857137197 : Rat) / 5120000000000000000000), D4 := ((783386318624999492653 : Rat) / 5120000000000000000000), LB := ((19779871654490577 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((13476465842910714281021 : Rat) / 5120000000000000000000), D0 := ((13476465842910714281021 : Rat) / 5120000000000000000000), D1 := ((4170993330910714281021 : Rat) / 5120000000000000000000), D2 := ((379838642910714281021 : Rat) / 5120000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((8694592921536237 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13476465842910714281021 : Rat) / 5120000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((454828246232142851523 : Rat) / 5120000000000000000000), D4 := ((780125901089285206979 : Rat) / 5120000000000000000000), LB := ((15430425634446743 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((2695945252089285713339 : Rat) / 1024000000000000000000), D0 := ((2695945252089285713339 : Rat) / 1024000000000000000000), D1 := ((834850749689285713339 : Rat) / 1024000000000000000000), D2 := ((76619812089285713339 : Rat) / 1024000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((695202838958131 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2695945252089285713339 : Rat) / 1024000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((451567828696428565849 : Rat) / 5120000000000000000000), D4 := ((155373096710714184261 : Rat) / 1024000000000000000000), LB := ((3202645161819867 : Rat) / 25000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((13482986677982142852369 : Rat) / 5120000000000000000000), D0 := ((13482986677982142852369 : Rat) / 5120000000000000000000), D1 := ((4177514165982142852369 : Rat) / 5120000000000000000000), D2 := ((386359477982142852369 : Rat) / 5120000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((3037633553209379 : Rat) / 25000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13482986677982142852369 : Rat) / 5120000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((17932296446428571207 : Rat) / 204800000000000000000), D4 := ((773605066017856635631 : Rat) / 5120000000000000000000), LB := ((2981122511740153 : Rat) / 25000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((13486247095517857138043 : Rat) / 5120000000000000000000), D0 := ((13486247095517857138043 : Rat) / 5120000000000000000000), D1 := ((4180774583517857138043 : Rat) / 5120000000000000000000), D2 := ((389619895517857138043 : Rat) / 5120000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((485322252939957 : Rat) / 4000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13486247095517857138043 : Rat) / 5120000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((445046993624999994501 : Rat) / 5120000000000000000000), D4 := ((770344648482142349957 : Rat) / 5120000000000000000000), LB := ((1277687683392259 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((13489507513053571423717 : Rat) / 5120000000000000000000), D0 := ((13489507513053571423717 : Rat) / 5120000000000000000000), D1 := ((4184035001053571423717 : Rat) / 5120000000000000000000), D2 := ((392880313053571423717 : Rat) / 5120000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((1385663101384771 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13489507513053571423717 : Rat) / 5120000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((441786576089285708827 : Rat) / 5120000000000000000000), D4 := ((767084230946428064283 : Rat) / 5120000000000000000000), LB := ((192162924747101 : Rat) / 1250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((13492767930589285709391 : Rat) / 5120000000000000000000), D0 := ((13492767930589285709391 : Rat) / 5120000000000000000000), D1 := ((4187295418589285709391 : Rat) / 5120000000000000000000), D2 := ((396140730589285709391 : Rat) / 5120000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((17326836576381233 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13492767930589285709391 : Rat) / 5120000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((438526158553571423153 : Rat) / 5120000000000000000000), D4 := ((763823813410713778609 : Rat) / 5120000000000000000000), LB := ((9859412717427851 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((2699205669624999999013 : Rat) / 1024000000000000000000), D0 := ((2699205669624999999013 : Rat) / 1024000000000000000000), D1 := ((838111167224999999013 : Rat) / 1024000000000000000000), D2 := ((79880229624999999013 : Rat) / 1024000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((22549823041095873 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2699205669624999999013 : Rat) / 1024000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((435265741017857137479 : Rat) / 5120000000000000000000), D4 := ((152112679174999898587 : Rat) / 1024000000000000000000), LB := ((322758597692957 : Rat) / 1250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((13499288765660714280739 : Rat) / 5120000000000000000000), D0 := ((13499288765660714280739 : Rat) / 5120000000000000000000), D1 := ((4193816253660714280739 : Rat) / 5120000000000000000000), D2 := ((402661565660714280739 : Rat) / 5120000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((2953231420223523 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13499288765660714280739 : Rat) / 5120000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((86401064696428570361 : Rat) / 1024000000000000000000), D4 := ((757302978339285207261 : Rat) / 5120000000000000000000), LB := ((3368563277022507 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((13502549183196428566413 : Rat) / 5120000000000000000000), D0 := ((13502549183196428566413 : Rat) / 5120000000000000000000), D1 := ((4197076671196428566413 : Rat) / 5120000000000000000000), D2 := ((405921983196428566413 : Rat) / 5120000000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((2392600645243631 : Rat) / 6250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13502549183196428566413 : Rat) / 5120000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((428744905946428566131 : Rat) / 5120000000000000000000), D4 := ((754042560803570921587 : Rat) / 5120000000000000000000), LB := ((1083031250633179 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((13505809600732142852087 : Rat) / 5120000000000000000000), D0 := ((13505809600732142852087 : Rat) / 5120000000000000000000), D1 := ((4200337088732142852087 : Rat) / 5120000000000000000000), D2 := ((409182400732142852087 : Rat) / 5120000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((48805591526421277 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13505809600732142852087 : Rat) / 5120000000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((425484488410714280457 : Rat) / 5120000000000000000000), D4 := ((750782143267856635913 : Rat) / 5120000000000000000000), LB := ((5473571111247189 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((13509070018267857137761 : Rat) / 5120000000000000000000), D0 := ((13509070018267857137761 : Rat) / 5120000000000000000000), D1 := ((4203597506267857137761 : Rat) / 5120000000000000000000), D2 := ((412442818267857137761 : Rat) / 5120000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((1527818046401369 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13509070018267857137761 : Rat) / 5120000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((422224070874999994783 : Rat) / 5120000000000000000000), D4 := ((747521725732142350239 : Rat) / 5120000000000000000000), LB := ((849222172277439 : Rat) / 1250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((2702466087160714284687 : Rat) / 1024000000000000000000), D0 := ((2702466087160714284687 : Rat) / 1024000000000000000000), D1 := ((841371584760714284687 : Rat) / 1024000000000000000000), D2 := ((83140647160714284687 : Rat) / 1024000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((7521205404391607 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2702466087160714284687 : Rat) / 1024000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((418963653339285709109 : Rat) / 5120000000000000000000), D4 := ((148852261639285612913 : Rat) / 1024000000000000000000), LB := ((2073419677736249 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((13018199402672903 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((310113770333853 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((5082362238092719 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((905831151357013 : Rat) / 1250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((9595216335140377 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((3032336072763403 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((1353678356732142856599 : Rat) / 512000000000000000000), D0 := ((1353678356732142856599 : Rat) / 512000000000000000000), D1 := ((423131105532142856599 : Rat) / 512000000000000000000), D2 := ((44015636732142856599 : Rat) / 512000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((1856297215196423 : Rat) / 1250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1353678356732142856599 : Rat) / 512000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((197255260910714283277 : Rat) / 2560000000000000000000), D4 := ((71980817667857092201 : Rat) / 512000000000000000000), LB := ((8879863153900963 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((2852308315697827 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((12577354811885433 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((2022617394691173 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((71663763710067 : Rat) / 25000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((4249191699494531 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((2982375806521803 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((341112807425761 : Rat) / 62500000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((8293757620337211 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((11584686552061 : Rat) / 1953125000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((6857455135359153 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((797082349528213 : Rat) / 62500000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((1924787126516833 : Rat) / 100000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((12224666954087363 : Rat) / 100000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((274634298303571428571 : Rat) / 100000000000000000000), D0 := ((274634298303571428571 : Rat) / 100000000000000000000), D1 := ((92886788303571428571 : Rat) / 100000000000000000000), D2 := ((18840798303571428571 : Rat) / 100000000000000000000), D3 := ((2538710625000000201 : Rat) / 100000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((5658601235927457 : Rat) / 100000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((274634298303571428571 : Rat) / 100000000000000000000), R := ((220215180767857142897 : Rat) / 80000000000000000000), D0 := ((220215180767857142897 : Rat) / 80000000000000000000), D1 := ((74817172767857142897 : Rat) / 80000000000000000000), D2 := ((15580380767857142897 : Rat) / 80000000000000000000), D3 := ((2538710625000000201 : Rat) / 80000000000000000000), D4 := ((3814759196428561429 : Rat) / 100000000000000000000), LB := ((2570876777085139 : Rat) / 62500000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((220215180767857142897 : Rat) / 80000000000000000000), R := ((551807307232142857343 : Rat) / 200000000000000000000), D0 := ((551807307232142857343 : Rat) / 200000000000000000000), D1 := ((188312287232142857343 : Rat) / 200000000000000000000), D2 := ((40220307232142857343 : Rat) / 200000000000000000000), D3 := ((7616131875000000603 : Rat) / 200000000000000000000), D4 := ((2544065232142849103 : Rat) / 80000000000000000000), LB := ((2003664887740797 : Rat) / 200000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((551807307232142857343 : Rat) / 200000000000000000000), R := ((2209767939553571429573 : Rat) / 800000000000000000000), D0 := ((2209767939553571429573 : Rat) / 800000000000000000000), D1 := ((755787859553571429573 : Rat) / 800000000000000000000), D2 := ((163419939553571429573 : Rat) / 800000000000000000000), D3 := ((33003238125000002613 : Rat) / 800000000000000000000), D4 := ((5090807767857122657 : Rat) / 200000000000000000000), LB := ((5845496226645819 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2209767939553571429573 : Rat) / 800000000000000000000), R := ((4422074589732142859347 : Rat) / 1600000000000000000000), D0 := ((4422074589732142859347 : Rat) / 1600000000000000000000), D1 := ((1514114429732142859347 : Rat) / 1600000000000000000000), D2 := ((329378589732142859347 : Rat) / 1600000000000000000000), D3 := ((68545186875000005427 : Rat) / 1600000000000000000000), D4 := ((17824520446428490427 : Rat) / 800000000000000000000), LB := ((5731647374324411 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4422074589732142859347 : Rat) / 1600000000000000000000), R := ((1106153325089285714887 : Rat) / 400000000000000000000), D0 := ((1106153325089285714887 : Rat) / 400000000000000000000), D1 := ((379163285089285714887 : Rat) / 400000000000000000000), D2 := ((82979325089285714887 : Rat) / 400000000000000000000), D3 := ((17770974375000001407 : Rat) / 400000000000000000000), D4 := ((33110330267856980653 : Rat) / 1600000000000000000000), LB := ((8401740900370047 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1106153325089285714887 : Rat) / 400000000000000000000), R := ((8851765311339285719297 : Rat) / 3200000000000000000000), D0 := ((8851765311339285719297 : Rat) / 3200000000000000000000), D1 := ((3035844991339285719297 : Rat) / 3200000000000000000000), D2 := ((666373311339285719297 : Rat) / 3200000000000000000000), D3 := ((144706505625000011457 : Rat) / 3200000000000000000000), D4 := ((7642904910714245113 : Rat) / 400000000000000000000), LB := ((433868359966871 : Rat) / 156250000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8851765311339285719297 : Rat) / 3200000000000000000000), R := ((4427152010982142859749 : Rat) / 1600000000000000000000), D0 := ((4427152010982142859749 : Rat) / 1600000000000000000000), D1 := ((1519191850982142859749 : Rat) / 1600000000000000000000), D2 := ((334456010982142859749 : Rat) / 1600000000000000000000), D3 := ((73622608125000005829 : Rat) / 1600000000000000000000), D4 := ((58604528660713960703 : Rat) / 3200000000000000000000), LB := ((12868920121506533 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4427152010982142859749 : Rat) / 1600000000000000000000), R := ((17711146754553571439197 : Rat) / 6400000000000000000000), D0 := ((17711146754553571439197 : Rat) / 6400000000000000000000), D1 := ((6079306114553571439197 : Rat) / 6400000000000000000000), D2 := ((1340362754553571439197 : Rat) / 6400000000000000000000), D3 := ((297029143125000023517 : Rat) / 6400000000000000000000), D4 := ((28032909017856980251 : Rat) / 1600000000000000000000), LB := ((549096109981273 : Rat) / 250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17711146754553571439197 : Rat) / 6400000000000000000000), R := ((8856842732589285719699 : Rat) / 3200000000000000000000), D0 := ((8856842732589285719699 : Rat) / 3200000000000000000000), D1 := ((3040922412589285719699 : Rat) / 3200000000000000000000), D2 := ((671450732589285719699 : Rat) / 3200000000000000000000), D3 := ((149783926875000011859 : Rat) / 3200000000000000000000), D4 := ((109592925446427920803 : Rat) / 6400000000000000000000), LB := ((16063678025947659 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8856842732589285719699 : Rat) / 3200000000000000000000), R := ((17716224175803571439599 : Rat) / 6400000000000000000000), D0 := ((17716224175803571439599 : Rat) / 6400000000000000000000), D1 := ((6084383535803571439599 : Rat) / 6400000000000000000000), D2 := ((1345440175803571439599 : Rat) / 6400000000000000000000), D3 := ((302106564375000023919 : Rat) / 6400000000000000000000), D4 := ((53527107410713960301 : Rat) / 3200000000000000000000), LB := ((2135701611464591 : Rat) / 2000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17716224175803571439599 : Rat) / 6400000000000000000000), R := ((88593814432142857199 : Rat) / 32000000000000000000), D0 := ((88593814432142857199 : Rat) / 32000000000000000000), D1 := ((30434611232142857199 : Rat) / 32000000000000000000), D2 := ((6739894432142857199 : Rat) / 32000000000000000000), D3 := ((7616131875000000603 : Rat) / 160000000000000000000), D4 := ((104515504196427920401 : Rat) / 6400000000000000000000), LB := ((2912162351935421 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((88593814432142857199 : Rat) / 32000000000000000000), R := ((17721301597053571440001 : Rat) / 6400000000000000000000), D0 := ((17721301597053571440001 : Rat) / 6400000000000000000000), D1 := ((6089460957053571440001 : Rat) / 6400000000000000000000), D2 := ((1350517597053571440001 : Rat) / 6400000000000000000000), D3 := ((307183985625000024321 : Rat) / 6400000000000000000000), D4 := ((509883967857139601 : Rat) / 32000000000000000000), LB := ((189813034477751 : Rat) / 1250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17721301597053571440001 : Rat) / 6400000000000000000000), R := ((35445141904732142880203 : Rat) / 12800000000000000000000), D0 := ((35445141904732142880203 : Rat) / 12800000000000000000000), D1 := ((12181460624732142880203 : Rat) / 12800000000000000000000), D2 := ((2703573904732142880203 : Rat) / 12800000000000000000000), D3 := ((616906681875000048843 : Rat) / 12800000000000000000000), D4 := ((99438082946427919999 : Rat) / 6400000000000000000000), LB := ((133630592784751 : Rat) / 156250000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35445141904732142880203 : Rat) / 12800000000000000000000), R := ((8861920153839285720101 : Rat) / 3200000000000000000000), D0 := ((8861920153839285720101 : Rat) / 3200000000000000000000), D1 := ((3045999833839285720101 : Rat) / 3200000000000000000000), D2 := ((676528153839285720101 : Rat) / 3200000000000000000000), D3 := ((154861348125000012261 : Rat) / 3200000000000000000000), D4 := ((196337455267855839797 : Rat) / 12800000000000000000000), LB := ((687044032643469 : Rat) / 1000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8861920153839285720101 : Rat) / 3200000000000000000000), R := ((7090043865196428576121 : Rat) / 2560000000000000000000), D0 := ((7090043865196428576121 : Rat) / 2560000000000000000000), D1 := ((2437307609196428576121 : Rat) / 2560000000000000000000), D2 := ((541730265196428576121 : Rat) / 2560000000000000000000), D3 := ((124396820625000009849 : Rat) / 2560000000000000000000), D4 := ((48449686160713959899 : Rat) / 3200000000000000000000), LB := ((667304131533597 : Rat) / 1250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7090043865196428576121 : Rat) / 2560000000000000000000), R := ((17726379018303571440403 : Rat) / 6400000000000000000000), D0 := ((17726379018303571440403 : Rat) / 6400000000000000000000), D1 := ((6094538378303571440403 : Rat) / 6400000000000000000000), D2 := ((1355595018303571440403 : Rat) / 6400000000000000000000), D3 := ((312261406875000024723 : Rat) / 6400000000000000000000), D4 := ((38252006803571167879 : Rat) / 2560000000000000000000), LB := ((989797235092793 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17726379018303571440403 : Rat) / 6400000000000000000000), R := ((35455296747232142881007 : Rat) / 12800000000000000000000), D0 := ((35455296747232142881007 : Rat) / 12800000000000000000000), D1 := ((12191615467232142881007 : Rat) / 12800000000000000000000), D2 := ((2713728747232142881007 : Rat) / 12800000000000000000000), D3 := ((627061524375000049647 : Rat) / 12800000000000000000000), D4 := ((94360661696427919597 : Rat) / 6400000000000000000000), LB := ((5471372882097647 : Rat) / 20000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35455296747232142881007 : Rat) / 12800000000000000000000), R := ((4432229432232142860151 : Rat) / 1600000000000000000000), D0 := ((4432229432232142860151 : Rat) / 1600000000000000000000), D1 := ((1524269272232142860151 : Rat) / 1600000000000000000000), D2 := ((339533432232142860151 : Rat) / 1600000000000000000000), D3 := ((78700029375000006231 : Rat) / 1600000000000000000000), D4 := ((186182612767855838993 : Rat) / 12800000000000000000000), LB := ((8355179955185643 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4432229432232142860151 : Rat) / 1600000000000000000000), R := ((35460374168482142881409 : Rat) / 12800000000000000000000), D0 := ((35460374168482142881409 : Rat) / 12800000000000000000000), D1 := ((12196692888482142881409 : Rat) / 12800000000000000000000), D2 := ((2718806168482142881409 : Rat) / 12800000000000000000000), D3 := ((632138945625000050049 : Rat) / 12800000000000000000000), D4 := ((22955487767856979849 : Rat) / 1600000000000000000000), LB := ((1921216963374217 : Rat) / 25000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35460374168482142881409 : Rat) / 12800000000000000000000), R := ((3546291287910714288161 : Rat) / 1280000000000000000000), D0 := ((3546291287910714288161 : Rat) / 1280000000000000000000), D1 := ((1219923159910714288161 : Rat) / 1280000000000000000000), D2 := ((272134487910714288161 : Rat) / 1280000000000000000000), D3 := ((2538710625000000201 : Rat) / 51200000000000000000), D4 := ((181105191517855838591 : Rat) / 12800000000000000000000), LB := ((314339911189343 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3546291287910714288161 : Rat) / 1280000000000000000000), R := ((70928364468839285763421 : Rat) / 25600000000000000000000), D0 := ((70928364468839285763421 : Rat) / 25600000000000000000000), D1 := ((24401001908839285763421 : Rat) / 25600000000000000000000), D2 := ((5445228468839285763421 : Rat) / 25600000000000000000000), D3 := ((1271894023125000100701 : Rat) / 25600000000000000000000), D4 := ((17856648089285583839 : Rat) / 1280000000000000000000), LB := ((47374634269753413 : Rat) / 100000000000000000000) }
]

def block234RightChunk001L : Rat := ((511587 : Rat) / 200000)
def block234RightChunk001R : Rat := ((70928364468839285763421 : Rat) / 25600000000000000000000)

def block234RightChunk001Certificate : Bool :=
  allBoxesValid block234RightChunk001 &&
  coversFromBool block234RightChunk001 block234RightChunk001L block234RightChunk001R

theorem block234RightChunk001Certificate_eq_true :
    block234RightChunk001Certificate = true := by
  native_decide

def block234RightChunk002 : List RatBox := [
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((70928364468839285763421 : Rat) / 25600000000000000000000), R := ((35465451589732142881811 : Rat) / 12800000000000000000000), D0 := ((35465451589732142881811 : Rat) / 12800000000000000000000), D1 := ((12201770309732142881811 : Rat) / 12800000000000000000000), D2 := ((2723883589732142881811 : Rat) / 12800000000000000000000), D3 := ((637216366875000050451 : Rat) / 12800000000000000000000), D4 := ((354594251160711676579 : Rat) / 25600000000000000000000), LB := ((2255250017097199 : Rat) / 5000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35465451589732142881811 : Rat) / 12800000000000000000000), R := ((70933441890089285763823 : Rat) / 25600000000000000000000), D0 := ((70933441890089285763823 : Rat) / 25600000000000000000000), D1 := ((24406079330089285763823 : Rat) / 25600000000000000000000), D2 := ((5450305890089285763823 : Rat) / 25600000000000000000000), D3 := ((1276971444375000101103 : Rat) / 25600000000000000000000), D4 := ((176027770267855838189 : Rat) / 12800000000000000000000), LB := ((2704519642651379 : Rat) / 6250000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((70933441890089285763823 : Rat) / 25600000000000000000000), R := ((8866997575089285720503 : Rat) / 3200000000000000000000), D0 := ((8866997575089285720503 : Rat) / 3200000000000000000000), D1 := ((3051077255089285720503 : Rat) / 3200000000000000000000), D2 := ((681605575089285720503 : Rat) / 3200000000000000000000), D3 := ((159938769375000012663 : Rat) / 3200000000000000000000), D4 := ((349516829910711676177 : Rat) / 25600000000000000000000), LB := ((10470369999747431 : Rat) / 25000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8866997575089285720503 : Rat) / 3200000000000000000000), R := ((2837540772453571430569 : Rat) / 1024000000000000000000), D0 := ((2837540772453571430569 : Rat) / 1024000000000000000000), D1 := ((976446270053571430569 : Rat) / 1024000000000000000000), D2 := ((218215332453571430569 : Rat) / 1024000000000000000000), D3 := ((256409773125000020301 : Rat) / 5120000000000000000000), D4 := ((43372264910713959497 : Rat) / 3200000000000000000000), LB := ((4093751382861499 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2837540772453571430569 : Rat) / 1024000000000000000000), R := ((35470529010982142882213 : Rat) / 12800000000000000000000), D0 := ((35470529010982142882213 : Rat) / 12800000000000000000000), D1 := ((12206847730982142882213 : Rat) / 12800000000000000000000), D2 := ((2728961010982142882213 : Rat) / 12800000000000000000000), D3 := ((642293788125000050853 : Rat) / 12800000000000000000000), D4 := ((13777576346428467031 : Rat) / 1024000000000000000000), LB := ((202227738012567 : Rat) / 500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35470529010982142882213 : Rat) / 12800000000000000000000), R := ((70943596732589285764627 : Rat) / 25600000000000000000000), D0 := ((70943596732589285764627 : Rat) / 25600000000000000000000), D1 := ((24416234172589285764627 : Rat) / 25600000000000000000000), D2 := ((5460460732589285764627 : Rat) / 25600000000000000000000), D3 := ((1287126286875000101907 : Rat) / 25600000000000000000000), D4 := ((170950349017855837787 : Rat) / 12800000000000000000000), LB := ((10102707953127399 : Rat) / 25000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((70943596732589285764627 : Rat) / 25600000000000000000000), R := ((17736533860803571441207 : Rat) / 6400000000000000000000), D0 := ((17736533860803571441207 : Rat) / 6400000000000000000000), D1 := ((6104693220803571441207 : Rat) / 6400000000000000000000), D2 := ((1365749860803571441207 : Rat) / 6400000000000000000000), D3 := ((322416249375000025527 : Rat) / 6400000000000000000000), D4 := ((339361987410711675373 : Rat) / 25600000000000000000000), LB := ((1020968472132261 : Rat) / 2500000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17736533860803571441207 : Rat) / 6400000000000000000000), R := ((70948674153839285765029 : Rat) / 25600000000000000000000), D0 := ((70948674153839285765029 : Rat) / 25600000000000000000000), D1 := ((24421311593839285765029 : Rat) / 25600000000000000000000), D2 := ((5465538153839285765029 : Rat) / 25600000000000000000000), D3 := ((1292203708125000102309 : Rat) / 25600000000000000000000), D4 := ((84205819196427918793 : Rat) / 6400000000000000000000), LB := ((41734766567158577 : Rat) / 100000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((70948674153839285765029 : Rat) / 25600000000000000000000), R := ((7095121286446428576523 : Rat) / 2560000000000000000000), D0 := ((7095121286446428576523 : Rat) / 2560000000000000000000), D1 := ((2442385030446428576523 : Rat) / 2560000000000000000000), D2 := ((546807686446428576523 : Rat) / 2560000000000000000000), D3 := ((129474241875000010251 : Rat) / 2560000000000000000000), D4 := ((334284566160711674971 : Rat) / 25600000000000000000000), LB := ((4310454142474329 : Rat) / 10000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7095121286446428576523 : Rat) / 2560000000000000000000), R := ((70953751575089285765431 : Rat) / 25600000000000000000000), D0 := ((70953751575089285765431 : Rat) / 25600000000000000000000), D1 := ((24426389015089285765431 : Rat) / 25600000000000000000000), D2 := ((5470615575089285765431 : Rat) / 25600000000000000000000), D3 := ((1297281129375000102711 : Rat) / 25600000000000000000000), D4 := ((33174585553571167477 : Rat) / 2560000000000000000000), LB := ((22476911232963137 : Rat) / 50000000000000000000) },
  { w1 := ((1728200349153623 : Rat) / 2000000000000000), w2 := ((8389737035251137 : Rat) / 100000000000000000), w3 := ((35517186240389 : Rat) / 195312500000000), w4 := ((3538195218030811 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((70953751575089285765431 : Rat) / 25600000000000000000000), R := ((69293252232142857193 : Rat) / 25000000000000000000), D0 := ((69293252232142857193 : Rat) / 25000000000000000000), D1 := ((23856374732142857193 : Rat) / 25000000000000000000), D2 := ((5344877232142857193 : Rat) / 25000000000000000000), D3 := ((2538710625000000201 : Rat) / 50000000000000000000), D4 := ((329207144910711674569 : Rat) / 25600000000000000000000), LB := ((9457700976827077 : Rat) / 20000000000000000000) }
]

def block234RightChunk002L : Rat := ((70928364468839285763421 : Rat) / 25600000000000000000000)
def block234RightChunk002R : Rat := ((69293252232142857193 : Rat) / 25000000000000000000)

def block234RightChunk002Certificate : Bool :=
  allBoxesValid block234RightChunk002 &&
  coversFromBool block234RightChunk002 block234RightChunk002L block234RightChunk002R

theorem block234RightChunk002Certificate_eq_true :
    block234RightChunk002Certificate = true := by
  native_decide

def block234RightChainCertificate : Bool :=
  decide (
    block234RightL = ((17715345982142857163 : Rat) / 10000000000000000000) /\
    ((511587 : Rat) / 200000) = ((511587 : Rat) / 200000) /\
    ((70928364468839285763421 : Rat) / 25600000000000000000000) = ((70928364468839285763421 : Rat) / 25600000000000000000000) /\
    ((69293252232142857193 : Rat) / 25000000000000000000) = block234RightR)

theorem block234RightChainCertificate_eq_true :
    block234RightChainCertificate = true := by
  native_decide

def block234LeftBoxCount : Nat := boxCount block234LeftBoxes
def block234RightBoxCount : Nat := 211

def block234_rational_certificate : Prop :=
    block234LeftCertificate = true /\
    block234RightChainCertificate = true /\
    block234RightChunk000Certificate = true /\
    block234RightChunk001Certificate = true /\
    block234RightChunk002Certificate = true

theorem block234_rational_certificate_proof :
    block234_rational_certificate := by
  exact ⟨block234LeftCertificate_eq_true, block234RightChainCertificate_eq_true, block234RightChunk000Certificate_eq_true, block234RightChunk001Certificate_eq_true, block234RightChunk002Certificate_eq_true⟩

end Block234
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block234

open Set

def block234W1 : Rat := ((1728200349153623 : Rat) / 2000000000000000)
def block234W2 : Rat := ((8389737035251137 : Rat) / 100000000000000000)
def block234W3 : Rat := ((35517186240389 : Rat) / 195312500000000)
def block234W4 : Rat := ((3538195218030811 : Rat) / 50000000000000000)
def block234S1 : Rat := ((18174751 : Rat) / 10000000)
def block234S2 : Rat := ((511587 : Rat) / 200000)
def block234S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block234S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block234V (y : ℝ) : ℝ :=
  ratPotential block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4 y

def block234LeftParamsCertificate : Bool :=
  allBoxesSameParams block234LeftBoxes block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4

theorem block234LeftParamsCertificate_eq_true :
    block234LeftParamsCertificate = true := by
  native_decide

theorem block234_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234LeftL : ℝ) (block234LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  have hcert := block234LeftCertificate_eq_true
  unfold block234LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block234LeftBoxes) (lo := block234LeftL) (hi := block234LeftR)
    (w1 := block234W1) (w2 := block234W2) (w3 := block234W3) (w4 := block234W4)
    (s1 := block234S1) (s2 := block234S2) (s3 := block234S3) (s4 := block234S4)
    hboxes hcover block234LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block234RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block234RightChunk000 block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4

theorem block234RightChunk000ParamsCertificate_eq_true :
    block234RightChunk000ParamsCertificate = true := by
  native_decide

theorem block234_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234RightChunk000L : ℝ) (block234RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  have hcert := block234RightChunk000Certificate_eq_true
  unfold block234RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block234RightChunk000) (lo := block234RightChunk000L) (hi := block234RightChunk000R)
    (w1 := block234W1) (w2 := block234W2) (w3 := block234W3) (w4 := block234W4)
    (s1 := block234S1) (s2 := block234S2) (s3 := block234S3) (s4 := block234S4)
    hboxes hcover block234RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block234RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block234RightChunk001 block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4

theorem block234RightChunk001ParamsCertificate_eq_true :
    block234RightChunk001ParamsCertificate = true := by
  native_decide

theorem block234_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234RightChunk001L : ℝ) (block234RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  have hcert := block234RightChunk001Certificate_eq_true
  unfold block234RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block234RightChunk001) (lo := block234RightChunk001L) (hi := block234RightChunk001R)
    (w1 := block234W1) (w2 := block234W2) (w3 := block234W3) (w4 := block234W4)
    (s1 := block234S1) (s2 := block234S2) (s3 := block234S3) (s4 := block234S4)
    hboxes hcover block234RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block234RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block234RightChunk002 block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4

theorem block234RightChunk002ParamsCertificate_eq_true :
    block234RightChunk002ParamsCertificate = true := by
  native_decide

theorem block234_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234RightChunk002L : ℝ) (block234RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  have hcert := block234RightChunk002Certificate_eq_true
  unfold block234RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block234RightChunk002) (lo := block234RightChunk002L) (hi := block234RightChunk002R)
    (w1 := block234W1) (w2 := block234W2) (w3 := block234W3) (w4 := block234W4)
    (s1 := block234S1) (s2 := block234S2) (s3 := block234S3) (s4 := block234S4)
    hboxes hcover block234RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block234_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234RightL : ℝ) (block234RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  by_cases h0 : y ≤ (block234RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block234RightChunk000L : ℝ) (block234RightChunk000R : ℝ) := by
      have hL : (block234RightChunk000L : ℝ) = (block234RightL : ℝ) := by
        norm_num [block234RightChunk000L, block234RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block234_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block234RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block234RightChunk001L : ℝ) (block234RightChunk001R : ℝ) := by
        have hprev : (block234RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block234RightChunk001L : ℝ) = (block234RightChunk000R : ℝ) := by
          norm_num [block234RightChunk001L, block234RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block234_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block234RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block234RightChunk002L : ℝ) = (block234RightChunk001R : ℝ) := by
        norm_num [block234RightChunk002L, block234RightChunk001R]
      have hR : (block234RightChunk002R : ℝ) = (block234RightR : ℝ) := by
        norm_num [block234RightChunk002R, block234RightR]
      have hyc : y ∈ Icc (block234RightChunk002L : ℝ) (block234RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block234_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block234_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block234LeftL : ℝ) (block234LeftR : ℝ) →
    y ≠ 0 → y ≠ (block234S1 : ℝ) → y ≠ (block234S2 : ℝ) →
    y ≠ (block234S3 : ℝ) → y ≠ (block234S4 : ℝ) → 0 < block234V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block234RightL : ℝ) (block234RightR : ℝ) →
    y ≠ 0 → y ≠ (block234S1 : ℝ) → y ≠ (block234S2 : ℝ) →
    y ≠ (block234S3 : ℝ) → y ≠ (block234S4 : ℝ) → 0 < block234V y)

theorem block234_reallog_certificate_proof :
    block234_reallog_certificate := by
  exact ⟨block234_left_V_pos, block234_right_V_pos⟩

end Block234
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block234.block234V
#check Erdos1038Lean.M1817475.Block234.block234_left_V_pos
#check Erdos1038Lean.M1817475.Block234.block234_right_V_pos
#check Erdos1038Lean.M1817475.Block234.block234_reallog_certificate_proof
