/-
Self-contained Lean4Web paste file.
Block 91 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block091

def block091LeftL : Rat := ((9993622767857142867 : Rat) / 12500000000000000000)
def block091LeftR : Rat := ((39984265625000000039 : Rat) / 50000000000000000000)
def block091RightL : Rat := ((22493622767857142867 : Rat) / 12500000000000000000)
def block091RightR : Rat := ((139984265625000000039 : Rat) / 50000000000000000000)

def block091LeftBoxes : List RatBox := [
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9993622767857142867 : Rat) / 12500000000000000000), R := ((39984265625000000039 : Rat) / 50000000000000000000), D0 := ((39984265625000000039 : Rat) / 50000000000000000000), D1 := ((12724815982142857133 : Rat) / 12500000000000000000), D2 := ((21980564732142857133 : Rat) / 12500000000000000000), D3 := ((23444070669642857133 : Rat) / 12500000000000000000), D4 := ((24812509419642855883 : Rat) / 12500000000000000000), LB := ((2518876024750101 : Rat) / 6250000000000000000) }
]

def block091LeftCertificate : Bool :=
  allBoxesValid block091LeftBoxes &&
  coversFromBool block091LeftBoxes block091LeftL block091LeftR

theorem block091LeftCertificate_eq_true :
    block091LeftCertificate = true := by
  native_decide

def block091RightChunk000 : List RatBox := [
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((22493622767857142867 : Rat) / 12500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((224815982142857133 : Rat) / 12500000000000000000), D2 := ((9480564732142857133 : Rat) / 12500000000000000000), D3 := ((10944070669642857133 : Rat) / 12500000000000000000), D4 := ((12312509419642855883 : Rat) / 12500000000000000000), LB := ((2820151971326323 : Rat) / 200000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((3348167649115631 : Rat) / 20000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((209318019 : Rat) / 80000000), D0 := ((209318019 : Rat) / 80000000), D1 := ((63920011 : Rat) / 80000000), D2 := ((4683219 : Rat) / 80000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((2008348417369037 : Rat) / 10000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209318019 : Rat) / 80000000), R := ((423319257 : Rat) / 160000000), D0 := ((423319257 : Rat) / 160000000), D1 := ((132523241 : Rat) / 160000000), D2 := ((14049657 : Rat) / 160000000), D3 := ((4683219 : Rat) / 80000000), D4 := ((1680153374999999 : Rat) / 10000000000000000), LB := ((1270010486041921 : Rat) / 10000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423319257 : Rat) / 160000000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 160000000), D4 := ((1387452187499999 : Rat) / 10000000000000000), LB := ((3309048292631217 : Rat) / 100000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107000619 : Rat) / 40000000), R := ((215095988999999999 : Rat) / 80000000000000000), D0 := ((215095988999999999 : Rat) / 80000000000000000), D1 := ((69697980999999999 : Rat) / 80000000000000000), D2 := ((10461188999999999 : Rat) / 80000000000000000), D3 := ((1094750999999999 : Rat) / 80000000000000000), D4 := ((1094750999999999 : Rat) / 10000000000000000), LB := ((24674743444389913 : Rat) / 1000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((215095988999999999 : Rat) / 80000000000000000), R := ((431286728999999997 : Rat) / 160000000000000000), D0 := ((431286728999999997 : Rat) / 160000000000000000), D1 := ((140490712999999997 : Rat) / 160000000000000000), D2 := ((22017128999999997 : Rat) / 160000000000000000), D3 := ((3284252999999997 : Rat) / 160000000000000000), D4 := ((7663256999999993 : Rat) / 80000000000000000), LB := ((6071544079137181 : Rat) / 250000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((431286728999999997 : Rat) / 160000000000000000), R := ((108095369999999999 : Rat) / 40000000000000000), D0 := ((108095369999999999 : Rat) / 40000000000000000), D1 := ((35396365999999999 : Rat) / 40000000000000000), D2 := ((5777969999999999 : Rat) / 40000000000000000), D3 := ((1094750999999999 : Rat) / 40000000000000000), D4 := ((14231762999999987 : Rat) / 160000000000000000), LB := ((10436794853795561 : Rat) / 1000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((108095369999999999 : Rat) / 40000000000000000), R := ((865857710999999991 : Rat) / 320000000000000000), D0 := ((865857710999999991 : Rat) / 320000000000000000), D1 := ((284265678999999991 : Rat) / 320000000000000000), D2 := ((47318510999999991 : Rat) / 320000000000000000), D3 := ((9852758999999991 : Rat) / 320000000000000000), D4 := ((3284252999999997 : Rat) / 40000000000000000), LB := ((13499986539053377 : Rat) / 1000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((865857710999999991 : Rat) / 320000000000000000), R := ((86695246199999999 : Rat) / 32000000000000000), D0 := ((86695246199999999 : Rat) / 32000000000000000), D1 := ((28536042999999999 : Rat) / 32000000000000000), D2 := ((4841326199999999 : Rat) / 32000000000000000), D3 := ((1094750999999999 : Rat) / 32000000000000000), D4 := ((25179272999999977 : Rat) / 320000000000000000), LB := ((7984068610444317 : Rat) / 1000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((86695246199999999 : Rat) / 32000000000000000), R := ((868047212999999989 : Rat) / 320000000000000000), D0 := ((868047212999999989 : Rat) / 320000000000000000), D1 := ((286455180999999989 : Rat) / 320000000000000000), D2 := ((49508012999999989 : Rat) / 320000000000000000), D3 := ((12042260999999989 : Rat) / 320000000000000000), D4 := ((12042260999999989 : Rat) / 160000000000000000), LB := ((2959461814517117 : Rat) / 1000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((868047212999999989 : Rat) / 320000000000000000), R := ((1737189176999999977 : Rat) / 640000000000000000), D0 := ((1737189176999999977 : Rat) / 640000000000000000), D1 := ((574005112999999977 : Rat) / 640000000000000000), D2 := ((100110776999999977 : Rat) / 640000000000000000), D3 := ((25179272999999977 : Rat) / 640000000000000000), D4 := ((22989770999999979 : Rat) / 320000000000000000), LB := ((6064429258133441 : Rat) / 1000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1737189176999999977 : Rat) / 640000000000000000), R := ((217285490999999997 : Rat) / 80000000000000000), D0 := ((217285490999999997 : Rat) / 80000000000000000), D1 := ((71887482999999997 : Rat) / 80000000000000000), D2 := ((12650690999999997 : Rat) / 80000000000000000), D3 := ((3284252999999997 : Rat) / 80000000000000000), D4 := ((44884790999999959 : Rat) / 640000000000000000), LB := ((2008826335072933 : Rat) / 500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((217285490999999997 : Rat) / 80000000000000000), R := ((69575147159999999 : Rat) / 25600000000000000), D0 := ((69575147159999999 : Rat) / 25600000000000000), D1 := ((23047784599999999 : Rat) / 25600000000000000), D2 := ((4092011159999999 : Rat) / 25600000000000000), D3 := ((1094750999999999 : Rat) / 25600000000000000), D4 := ((1094750999999999 : Rat) / 16000000000000000), LB := ((4243216410587447 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((69575147159999999 : Rat) / 25600000000000000), R := ((870236714999999987 : Rat) / 320000000000000000), D0 := ((870236714999999987 : Rat) / 320000000000000000), D1 := ((288644682999999987 : Rat) / 320000000000000000), D2 := ((51697514999999987 : Rat) / 320000000000000000), D3 := ((14231762999999987 : Rat) / 320000000000000000), D4 := ((42695288999999961 : Rat) / 640000000000000000), LB := ((957967719402153 : Rat) / 2500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((870236714999999987 : Rat) / 320000000000000000), R := ((3482041610999999947 : Rat) / 1280000000000000000), D0 := ((3482041610999999947 : Rat) / 1280000000000000000), D1 := ((1155673482999999947 : Rat) / 1280000000000000000), D2 := ((207884810999999947 : Rat) / 1280000000000000000), D3 := ((58021802999999947 : Rat) / 1280000000000000000), D4 := ((20800268999999981 : Rat) / 320000000000000000), LB := ((25867893606185133 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3482041610999999947 : Rat) / 1280000000000000000), R := ((1741568180999999973 : Rat) / 640000000000000000), D0 := ((1741568180999999973 : Rat) / 640000000000000000), D1 := ((578384116999999973 : Rat) / 640000000000000000), D2 := ((104489780999999973 : Rat) / 640000000000000000), D3 := ((29558276999999973 : Rat) / 640000000000000000), D4 := ((3284252999999997 : Rat) / 51200000000000000), LB := ((18611132617438741 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1741568180999999973 : Rat) / 640000000000000000), R := ((696846222599999989 : Rat) / 256000000000000000), D0 := ((696846222599999989 : Rat) / 256000000000000000), D1 := ((231572596999999989 : Rat) / 256000000000000000), D2 := ((42014862599999989 : Rat) / 256000000000000000), D3 := ((12042260999999989 : Rat) / 256000000000000000), D4 := ((40505786999999963 : Rat) / 640000000000000000), LB := ((5898847646690353 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((696846222599999989 : Rat) / 256000000000000000), R := ((435665732999999993 : Rat) / 160000000000000000), D0 := ((435665732999999993 : Rat) / 160000000000000000), D1 := ((144869716999999993 : Rat) / 160000000000000000), D2 := ((26396132999999993 : Rat) / 160000000000000000), D3 := ((7663256999999993 : Rat) / 160000000000000000), D4 := ((79916822999999927 : Rat) / 1280000000000000000), LB := ((5438664689300099 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((435665732999999993 : Rat) / 160000000000000000), R := ((6971746478999999887 : Rat) / 2560000000000000000), D0 := ((6971746478999999887 : Rat) / 2560000000000000000), D1 := ((2319010222999999887 : Rat) / 2560000000000000000), D2 := ((423432878999999887 : Rat) / 2560000000000000000), D3 := ((123706862999999887 : Rat) / 2560000000000000000), D4 := ((9852758999999991 : Rat) / 160000000000000000), LB := ((2296963110800937 : Rat) / 1250000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6971746478999999887 : Rat) / 2560000000000000000), R := ((3486420614999999943 : Rat) / 1280000000000000000), D0 := ((3486420614999999943 : Rat) / 1280000000000000000), D1 := ((1160052486999999943 : Rat) / 1280000000000000000), D2 := ((212263814999999943 : Rat) / 1280000000000000000), D3 := ((62400806999999943 : Rat) / 1280000000000000000), D4 := ((156549392999999857 : Rat) / 2560000000000000000), LB := ((1559924821853631 : Rat) / 1000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3486420614999999943 : Rat) / 1280000000000000000), R := ((1394787196199999977 : Rat) / 512000000000000000), D0 := ((1394787196199999977 : Rat) / 512000000000000000), D1 := ((464239944999999977 : Rat) / 512000000000000000), D2 := ((85124476199999977 : Rat) / 512000000000000000), D3 := ((25179272999999977 : Rat) / 512000000000000000), D4 := ((77727320999999929 : Rat) / 1280000000000000000), LB := ((103550708173481 : Rat) / 80000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1394787196199999977 : Rat) / 512000000000000000), R := ((1743757682999999971 : Rat) / 640000000000000000), D0 := ((1743757682999999971 : Rat) / 640000000000000000), D1 := ((580573618999999971 : Rat) / 640000000000000000), D2 := ((106679282999999971 : Rat) / 640000000000000000), D3 := ((31747778999999971 : Rat) / 640000000000000000), D4 := ((154359890999999859 : Rat) / 2560000000000000000), LB := ((1301382550229907 : Rat) / 1250000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1743757682999999971 : Rat) / 640000000000000000), R := ((6976125482999999883 : Rat) / 2560000000000000000), D0 := ((6976125482999999883 : Rat) / 2560000000000000000), D1 := ((2323389226999999883 : Rat) / 2560000000000000000), D2 := ((427811882999999883 : Rat) / 2560000000000000000), D3 := ((128085866999999883 : Rat) / 2560000000000000000), D4 := ((7663256999999993 : Rat) / 128000000000000000), LB := ((8002532477061619 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6976125482999999883 : Rat) / 2560000000000000000), R := ((3488610116999999941 : Rat) / 1280000000000000000), D0 := ((3488610116999999941 : Rat) / 1280000000000000000), D1 := ((1162241988999999941 : Rat) / 1280000000000000000), D2 := ((214453316999999941 : Rat) / 1280000000000000000), D3 := ((64590308999999941 : Rat) / 1280000000000000000), D4 := ((152170388999999861 : Rat) / 2560000000000000000), LB := ((1429977088107659 : Rat) / 2500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3488610116999999941 : Rat) / 1280000000000000000), R := ((6978314984999999881 : Rat) / 2560000000000000000), D0 := ((6978314984999999881 : Rat) / 2560000000000000000), D1 := ((2325578728999999881 : Rat) / 2560000000000000000), D2 := ((430001384999999881 : Rat) / 2560000000000000000), D3 := ((130275368999999881 : Rat) / 2560000000000000000), D4 := ((75537818999999931 : Rat) / 1280000000000000000), LB := ((1782438815096099 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6978314984999999881 : Rat) / 2560000000000000000), R := ((174485243399999997 : Rat) / 64000000000000000), D0 := ((174485243399999997 : Rat) / 64000000000000000), D1 := ((58166836999999997 : Rat) / 64000000000000000), D2 := ((10777403399999997 : Rat) / 64000000000000000), D3 := ((3284252999999997 : Rat) / 64000000000000000), D4 := ((149980886999999863 : Rat) / 2560000000000000000), LB := ((1923958695757011 : Rat) / 12500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((174485243399999997 : Rat) / 64000000000000000), R := ((13959914222999999759 : Rat) / 5120000000000000000), D0 := ((13959914222999999759 : Rat) / 5120000000000000000), D1 := ((4654441710999999759 : Rat) / 5120000000000000000), D2 := ((863287022999999759 : Rat) / 5120000000000000000), D3 := ((263834990999999759 : Rat) / 5120000000000000000), D4 := ((18610766999999983 : Rat) / 320000000000000000), LB := ((9029279167913629 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13959914222999999759 : Rat) / 5120000000000000000), R := ((6980504486999999879 : Rat) / 2560000000000000000), D0 := ((6980504486999999879 : Rat) / 2560000000000000000), D1 := ((2327768230999999879 : Rat) / 2560000000000000000), D2 := ((432190886999999879 : Rat) / 2560000000000000000), D3 := ((132464870999999879 : Rat) / 2560000000000000000), D4 := ((296677520999999729 : Rat) / 5120000000000000000), LB := ((1625920314241247 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6980504486999999879 : Rat) / 2560000000000000000), R := ((13962103724999999757 : Rat) / 5120000000000000000), D0 := ((13962103724999999757 : Rat) / 5120000000000000000), D1 := ((4656631212999999757 : Rat) / 5120000000000000000), D2 := ((865476524999999757 : Rat) / 5120000000000000000), D3 := ((266024492999999757 : Rat) / 5120000000000000000), D4 := ((29558276999999973 : Rat) / 512000000000000000), LB := ((3631687891076929 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13962103724999999757 : Rat) / 5120000000000000000), R := ((3490799618999999939 : Rat) / 1280000000000000000), D0 := ((3490799618999999939 : Rat) / 1280000000000000000), D1 := ((1164431490999999939 : Rat) / 1280000000000000000), D2 := ((216642818999999939 : Rat) / 1280000000000000000), D3 := ((66779810999999939 : Rat) / 1280000000000000000), D4 := ((294488018999999731 : Rat) / 5120000000000000000), LB := ((1286166725769311 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3490799618999999939 : Rat) / 1280000000000000000), R := ((2792858645399999951 : Rat) / 1024000000000000000), D0 := ((2792858645399999951 : Rat) / 1024000000000000000), D1 := ((931764142999999951 : Rat) / 1024000000000000000), D2 := ((173533205399999951 : Rat) / 1024000000000000000), D3 := ((53642798999999951 : Rat) / 1024000000000000000), D4 := ((73348316999999933 : Rat) / 1280000000000000000), LB := ((281610477051053 : Rat) / 500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2792858645399999951 : Rat) / 1024000000000000000), R := ((6982693988999999877 : Rat) / 2560000000000000000), D0 := ((6982693988999999877 : Rat) / 2560000000000000000), D1 := ((2329957732999999877 : Rat) / 2560000000000000000), D2 := ((434380388999999877 : Rat) / 2560000000000000000), D3 := ((134654372999999877 : Rat) / 2560000000000000000), D4 := ((292298516999999733 : Rat) / 5120000000000000000), LB := ((4867740589022951 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6982693988999999877 : Rat) / 2560000000000000000), R := ((13966482728999999753 : Rat) / 5120000000000000000), D0 := ((13966482728999999753 : Rat) / 5120000000000000000), D1 := ((4661010216999999753 : Rat) / 5120000000000000000), D2 := ((869855528999999753 : Rat) / 5120000000000000000), D3 := ((270403496999999753 : Rat) / 5120000000000000000), D4 := ((145601882999999867 : Rat) / 2560000000000000000), LB := ((165506660933179 : Rat) / 400000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13966482728999999753 : Rat) / 5120000000000000000), R := ((1745947184999999969 : Rat) / 640000000000000000), D0 := ((1745947184999999969 : Rat) / 640000000000000000), D1 := ((582763120999999969 : Rat) / 640000000000000000), D2 := ((108868784999999969 : Rat) / 640000000000000000), D3 := ((33937280999999969 : Rat) / 640000000000000000), D4 := ((58021802999999947 : Rat) / 1024000000000000000), LB := ((3442229814992759 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1745947184999999969 : Rat) / 640000000000000000), R := ((13968672230999999751 : Rat) / 5120000000000000000), D0 := ((13968672230999999751 : Rat) / 5120000000000000000), D1 := ((4663199718999999751 : Rat) / 5120000000000000000), D2 := ((872045030999999751 : Rat) / 5120000000000000000), D3 := ((272592998999999751 : Rat) / 5120000000000000000), D4 := ((36126782999999967 : Rat) / 640000000000000000), LB := ((6954189241994979 : Rat) / 25000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13968672230999999751 : Rat) / 5120000000000000000), R := ((55879067927999999 : Rat) / 20480000000000000), D0 := ((55879067927999999 : Rat) / 20480000000000000), D1 := ((18657177879999999 : Rat) / 20480000000000000), D2 := ((3492559127999999 : Rat) / 20480000000000000), D3 := ((1094750999999999 : Rat) / 20480000000000000), D4 := ((287919512999999737 : Rat) / 5120000000000000000), LB := ((336914407044267 : Rat) / 1562500000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((55879067927999999 : Rat) / 20480000000000000), R := ((13970861732999999749 : Rat) / 5120000000000000000), D0 := ((13970861732999999749 : Rat) / 5120000000000000000), D1 := ((4665389220999999749 : Rat) / 5120000000000000000), D2 := ((874234532999999749 : Rat) / 5120000000000000000), D3 := ((274782500999999749 : Rat) / 5120000000000000000), D4 := ((143412380999999869 : Rat) / 2560000000000000000), LB := ((3915525556286159 : Rat) / 25000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13970861732999999749 : Rat) / 5120000000000000000), R := ((3492989120999999937 : Rat) / 1280000000000000000), D0 := ((3492989120999999937 : Rat) / 1280000000000000000), D1 := ((1166620992999999937 : Rat) / 1280000000000000000), D2 := ((218832320999999937 : Rat) / 1280000000000000000), D3 := ((68969312999999937 : Rat) / 1280000000000000000), D4 := ((285730010999999739 : Rat) / 5120000000000000000), LB := ((10118035215878063 : Rat) / 100000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3492989120999999937 : Rat) / 1280000000000000000), R := ((13973051234999999747 : Rat) / 5120000000000000000), D0 := ((13973051234999999747 : Rat) / 5120000000000000000), D1 := ((4667578722999999747 : Rat) / 5120000000000000000), D2 := ((876424034999999747 : Rat) / 5120000000000000000), D3 := ((276972002999999747 : Rat) / 5120000000000000000), D4 := ((14231762999999987 : Rat) / 256000000000000000), LB := ((2466444045162719 : Rat) / 50000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13973051234999999747 : Rat) / 5120000000000000000), R := ((6987072992999999873 : Rat) / 2560000000000000000), D0 := ((6987072992999999873 : Rat) / 2560000000000000000), D1 := ((2334336736999999873 : Rat) / 2560000000000000000), D2 := ((438759392999999873 : Rat) / 2560000000000000000), D3 := ((139033376999999873 : Rat) / 2560000000000000000), D4 := ((283540508999999741 : Rat) / 5120000000000000000), LB := ((5462885488416447 : Rat) / 5000000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6987072992999999873 : Rat) / 2560000000000000000), R := ((27949386722999999491 : Rat) / 10240000000000000000), D0 := ((27949386722999999491 : Rat) / 10240000000000000000), D1 := ((9338441698999999491 : Rat) / 10240000000000000000), D2 := ((1756132322999999491 : Rat) / 10240000000000000000), D3 := ((557228258999999491 : Rat) / 10240000000000000000), D4 := ((141222878999999871 : Rat) / 2560000000000000000), LB := ((1060895162825759 : Rat) / 2500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27949386722999999491 : Rat) / 10240000000000000000), R := ((2795048147399999949 : Rat) / 1024000000000000000), D0 := ((2795048147399999949 : Rat) / 1024000000000000000), D1 := ((933953644999999949 : Rat) / 1024000000000000000), D2 := ((175722707399999949 : Rat) / 1024000000000000000), D3 := ((55832300999999949 : Rat) / 1024000000000000000), D4 := ((112759352999999897 : Rat) / 2048000000000000000), LB := ((8067653691119503 : Rat) / 20000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2795048147399999949 : Rat) / 1024000000000000000), R := ((27951576224999999489 : Rat) / 10240000000000000000), D0 := ((27951576224999999489 : Rat) / 10240000000000000000), D1 := ((9340631200999999489 : Rat) / 10240000000000000000), D2 := ((1758321824999999489 : Rat) / 10240000000000000000), D3 := ((559417760999999489 : Rat) / 10240000000000000000), D4 := ((281351006999999743 : Rat) / 5120000000000000000), LB := ((1916638333510079 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27951576224999999489 : Rat) / 10240000000000000000), R := ((54595060499999999 : Rat) / 20000000000000000), D0 := ((54595060499999999 : Rat) / 20000000000000000), D1 := ((18245558499999999 : Rat) / 20000000000000000), D2 := ((3436360499999999 : Rat) / 20000000000000000), D3 := ((1094750999999999 : Rat) / 20000000000000000), D4 := ((561607262999999487 : Rat) / 10240000000000000000), LB := ((3641963826614969 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54595060499999999 : Rat) / 20000000000000000), R := ((27953765726999999487 : Rat) / 10240000000000000000), D0 := ((27953765726999999487 : Rat) / 10240000000000000000), D1 := ((9342820702999999487 : Rat) / 10240000000000000000), D2 := ((1760511326999999487 : Rat) / 10240000000000000000), D3 := ((561607262999999487 : Rat) / 10240000000000000000), D4 := ((1094750999999999 : Rat) / 20000000000000000), LB := ((691984446667071 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27953765726999999487 : Rat) / 10240000000000000000), R := ((13977430238999999743 : Rat) / 5120000000000000000), D0 := ((13977430238999999743 : Rat) / 5120000000000000000), D1 := ((4671957726999999743 : Rat) / 5120000000000000000), D2 := ((880803038999999743 : Rat) / 5120000000000000000), D3 := ((281351006999999743 : Rat) / 5120000000000000000), D4 := ((559417760999999489 : Rat) / 10240000000000000000), LB := ((3287185995771713 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13977430238999999743 : Rat) / 5120000000000000000), R := ((5591191045799999897 : Rat) / 2048000000000000000), D0 := ((5591191045799999897 : Rat) / 2048000000000000000), D1 := ((1869002040999999897 : Rat) / 2048000000000000000), D2 := ((352540165799999897 : Rat) / 2048000000000000000), D3 := ((112759352999999897 : Rat) / 2048000000000000000), D4 := ((55832300999999949 : Rat) / 1024000000000000000), LB := ((3904736779640483 : Rat) / 12500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5591191045799999897 : Rat) / 2048000000000000000), R := ((6989262494999999871 : Rat) / 2560000000000000000), D0 := ((6989262494999999871 : Rat) / 2560000000000000000), D1 := ((2336526238999999871 : Rat) / 2560000000000000000), D2 := ((440948894999999871 : Rat) / 2560000000000000000), D3 := ((141222878999999871 : Rat) / 2560000000000000000), D4 := ((557228258999999491 : Rat) / 10240000000000000000), LB := ((1484883514847879 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6989262494999999871 : Rat) / 2560000000000000000), R := ((27958144730999999483 : Rat) / 10240000000000000000), D0 := ((27958144730999999483 : Rat) / 10240000000000000000), D1 := ((9347199706999999483 : Rat) / 10240000000000000000), D2 := ((1764890330999999483 : Rat) / 10240000000000000000), D3 := ((565986266999999483 : Rat) / 10240000000000000000), D4 := ((139033376999999873 : Rat) / 2560000000000000000), LB := ((706288382659459 : Rat) / 2500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27958144730999999483 : Rat) / 10240000000000000000), R := ((13979619740999999741 : Rat) / 5120000000000000000), D0 := ((13979619740999999741 : Rat) / 5120000000000000000), D1 := ((4674147228999999741 : Rat) / 5120000000000000000), D2 := ((882992540999999741 : Rat) / 5120000000000000000), D3 := ((283540508999999741 : Rat) / 5120000000000000000), D4 := ((555038756999999493 : Rat) / 10240000000000000000), LB := ((1344991924712713 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13979619740999999741 : Rat) / 5120000000000000000), R := ((27960334232999999481 : Rat) / 10240000000000000000), D0 := ((27960334232999999481 : Rat) / 10240000000000000000), D1 := ((9349389208999999481 : Rat) / 10240000000000000000), D2 := ((1767079832999999481 : Rat) / 10240000000000000000), D3 := ((568175768999999481 : Rat) / 10240000000000000000), D4 := ((276972002999999747 : Rat) / 5120000000000000000), LB := ((512858623299639 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27960334232999999481 : Rat) / 10240000000000000000), R := ((699035724599999987 : Rat) / 256000000000000000), D0 := ((699035724599999987 : Rat) / 256000000000000000), D1 := ((233762098999999987 : Rat) / 256000000000000000), D2 := ((44204364599999987 : Rat) / 256000000000000000), D3 := ((14231762999999987 : Rat) / 256000000000000000), D4 := ((110569850999999899 : Rat) / 2048000000000000000), LB := ((2448116671572853 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((699035724599999987 : Rat) / 256000000000000000), R := ((27962523734999999479 : Rat) / 10240000000000000000), D0 := ((27962523734999999479 : Rat) / 10240000000000000000), D1 := ((9351578710999999479 : Rat) / 10240000000000000000), D2 := ((1769269334999999479 : Rat) / 10240000000000000000), D3 := ((570365270999999479 : Rat) / 10240000000000000000), D4 := ((68969312999999937 : Rat) / 1280000000000000000), LB := ((23414900652307669 : Rat) / 100000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27962523734999999479 : Rat) / 10240000000000000000), R := ((13981809242999999739 : Rat) / 5120000000000000000), D0 := ((13981809242999999739 : Rat) / 5120000000000000000), D1 := ((4676336730999999739 : Rat) / 5120000000000000000), D2 := ((885182042999999739 : Rat) / 5120000000000000000), D3 := ((285730010999999739 : Rat) / 5120000000000000000), D4 := ((550659752999999497 : Rat) / 10240000000000000000), LB := ((2244449060658793 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13981809242999999739 : Rat) / 5120000000000000000), R := ((27964713236999999477 : Rat) / 10240000000000000000), D0 := ((27964713236999999477 : Rat) / 10240000000000000000), D1 := ((9353768212999999477 : Rat) / 10240000000000000000), D2 := ((1771458836999999477 : Rat) / 10240000000000000000), D3 := ((572554772999999477 : Rat) / 10240000000000000000), D4 := ((274782500999999749 : Rat) / 5120000000000000000), LB := ((21570296352579899 : Rat) / 100000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27964713236999999477 : Rat) / 10240000000000000000), R := ((6991451996999999869 : Rat) / 2560000000000000000), D0 := ((6991451996999999869 : Rat) / 2560000000000000000), D1 := ((2338715740999999869 : Rat) / 2560000000000000000), D2 := ((443138396999999869 : Rat) / 2560000000000000000), D3 := ((143412380999999869 : Rat) / 2560000000000000000), D4 := ((548470250999999499 : Rat) / 10240000000000000000), LB := ((20792679824432891 : Rat) / 100000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6991451996999999869 : Rat) / 2560000000000000000), R := ((1118676109559999979 : Rat) / 409600000000000000), D0 := ((1118676109559999979 : Rat) / 409600000000000000), D1 := ((374238308599999979 : Rat) / 409600000000000000), D2 := ((70945933559999979 : Rat) / 409600000000000000), D3 := ((22989770999999979 : Rat) / 409600000000000000), D4 := ((1094750999999999 : Rat) / 20480000000000000), LB := ((4022401026546607 : Rat) / 20000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1118676109559999979 : Rat) / 409600000000000000), R := ((13983998744999999737 : Rat) / 5120000000000000000), D0 := ((13983998744999999737 : Rat) / 5120000000000000000), D1 := ((4678526232999999737 : Rat) / 5120000000000000000), D2 := ((887371544999999737 : Rat) / 5120000000000000000), D3 := ((287919512999999737 : Rat) / 5120000000000000000), D4 := ((546280748999999501 : Rat) / 10240000000000000000), LB := ((976431929159971 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13983998744999999737 : Rat) / 5120000000000000000), R := ((27969092240999999473 : Rat) / 10240000000000000000), D0 := ((27969092240999999473 : Rat) / 10240000000000000000), D1 := ((9358147216999999473 : Rat) / 10240000000000000000), D2 := ((1775837840999999473 : Rat) / 10240000000000000000), D3 := ((576933776999999473 : Rat) / 10240000000000000000), D4 := ((272592998999999751 : Rat) / 5120000000000000000), LB := ((9521474346296799 : Rat) / 50000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27969092240999999473 : Rat) / 10240000000000000000), R := ((1748136686999999967 : Rat) / 640000000000000000), D0 := ((1748136686999999967 : Rat) / 640000000000000000), D1 := ((584952622999999967 : Rat) / 640000000000000000), D2 := ((111058286999999967 : Rat) / 640000000000000000), D3 := ((36126782999999967 : Rat) / 640000000000000000), D4 := ((544091246999999503 : Rat) / 10240000000000000000), LB := ((4663826552095407 : Rat) / 25000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1748136686999999967 : Rat) / 640000000000000000), R := ((27971281742999999471 : Rat) / 10240000000000000000), D0 := ((27971281742999999471 : Rat) / 10240000000000000000), D1 := ((9360336718999999471 : Rat) / 10240000000000000000), D2 := ((1778027342999999471 : Rat) / 10240000000000000000), D3 := ((579123278999999471 : Rat) / 10240000000000000000), D4 := ((33937280999999969 : Rat) / 640000000000000000), LB := ((4591521031283019 : Rat) / 25000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27971281742999999471 : Rat) / 10240000000000000000), R := ((2797237649399999947 : Rat) / 1024000000000000000), D0 := ((2797237649399999947 : Rat) / 1024000000000000000), D1 := ((936143146999999947 : Rat) / 1024000000000000000), D2 := ((177912209399999947 : Rat) / 1024000000000000000), D3 := ((58021802999999947 : Rat) / 1024000000000000000), D4 := ((108380348999999901 : Rat) / 2048000000000000000), LB := ((567989303233013 : Rat) / 3125000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2797237649399999947 : Rat) / 1024000000000000000), R := ((27973471244999999469 : Rat) / 10240000000000000000), D0 := ((27973471244999999469 : Rat) / 10240000000000000000), D1 := ((9362526220999999469 : Rat) / 10240000000000000000), D2 := ((1780216844999999469 : Rat) / 10240000000000000000), D3 := ((581312780999999469 : Rat) / 10240000000000000000), D4 := ((270403496999999753 : Rat) / 5120000000000000000), LB := ((904220224409169 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27973471244999999469 : Rat) / 10240000000000000000), R := ((6993641498999999867 : Rat) / 2560000000000000000), D0 := ((6993641498999999867 : Rat) / 2560000000000000000), D1 := ((2340905242999999867 : Rat) / 2560000000000000000), D2 := ((445327898999999867 : Rat) / 2560000000000000000), D3 := ((145601882999999867 : Rat) / 2560000000000000000), D4 := ((539712242999999507 : Rat) / 10240000000000000000), LB := ((9046352163433191 : Rat) / 50000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6993641498999999867 : Rat) / 2560000000000000000), R := ((27975660746999999467 : Rat) / 10240000000000000000), D0 := ((27975660746999999467 : Rat) / 10240000000000000000), D1 := ((9364715722999999467 : Rat) / 10240000000000000000), D2 := ((1782406346999999467 : Rat) / 10240000000000000000), D3 := ((583502282999999467 : Rat) / 10240000000000000000), D4 := ((134654372999999877 : Rat) / 2560000000000000000), LB := ((1137558711779979 : Rat) / 6250000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27975660746999999467 : Rat) / 10240000000000000000), R := ((13988377748999999733 : Rat) / 5120000000000000000), D0 := ((13988377748999999733 : Rat) / 5120000000000000000), D1 := ((4682905236999999733 : Rat) / 5120000000000000000), D2 := ((891750548999999733 : Rat) / 5120000000000000000), D3 := ((292298516999999733 : Rat) / 5120000000000000000), D4 := ((537522740999999509 : Rat) / 10240000000000000000), LB := ((2301186772768471 : Rat) / 12500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13988377748999999733 : Rat) / 5120000000000000000), R := ((5595570049799999893 : Rat) / 2048000000000000000), D0 := ((5595570049799999893 : Rat) / 2048000000000000000), D1 := ((1873381044999999893 : Rat) / 2048000000000000000), D2 := ((356919169799999893 : Rat) / 2048000000000000000), D3 := ((117138356999999893 : Rat) / 2048000000000000000), D4 := ((53642798999999951 : Rat) / 1024000000000000000), LB := ((9359377788276113 : Rat) / 50000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5595570049799999893 : Rat) / 2048000000000000000), R := ((3497368124999999933 : Rat) / 1280000000000000000), D0 := ((3497368124999999933 : Rat) / 1280000000000000000), D1 := ((1170999996999999933 : Rat) / 1280000000000000000), D2 := ((223211324999999933 : Rat) / 1280000000000000000), D3 := ((73348316999999933 : Rat) / 1280000000000000000), D4 := ((535333238999999511 : Rat) / 10240000000000000000), LB := ((4782278204695789 : Rat) / 25000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3497368124999999933 : Rat) / 1280000000000000000), R := ((27980039750999999463 : Rat) / 10240000000000000000), D0 := ((27980039750999999463 : Rat) / 10240000000000000000), D1 := ((9369094726999999463 : Rat) / 10240000000000000000), D2 := ((1786785350999999463 : Rat) / 10240000000000000000), D3 := ((587881286999999463 : Rat) / 10240000000000000000), D4 := ((66779810999999939 : Rat) / 1280000000000000000), LB := ((3928191510911283 : Rat) / 20000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27980039750999999463 : Rat) / 10240000000000000000), R := ((13990567250999999731 : Rat) / 5120000000000000000), D0 := ((13990567250999999731 : Rat) / 5120000000000000000), D1 := ((4685094738999999731 : Rat) / 5120000000000000000), D2 := ((893940050999999731 : Rat) / 5120000000000000000), D3 := ((294488018999999731 : Rat) / 5120000000000000000), D4 := ((533143736999999513 : Rat) / 10240000000000000000), LB := ((10127341923249489 : Rat) / 50000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13990567250999999731 : Rat) / 5120000000000000000), R := ((27982229252999999461 : Rat) / 10240000000000000000), D0 := ((27982229252999999461 : Rat) / 10240000000000000000), D1 := ((9371284228999999461 : Rat) / 10240000000000000000), D2 := ((1788974852999999461 : Rat) / 10240000000000000000), D3 := ((590070788999999461 : Rat) / 10240000000000000000), D4 := ((266024492999999757 : Rat) / 5120000000000000000), LB := ((5242672049007857 : Rat) / 25000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27982229252999999461 : Rat) / 10240000000000000000), R := ((1399166200199999973 : Rat) / 512000000000000000), D0 := ((1399166200199999973 : Rat) / 512000000000000000), D1 := ((468618948999999973 : Rat) / 512000000000000000), D2 := ((89503480199999973 : Rat) / 512000000000000000), D3 := ((29558276999999973 : Rat) / 512000000000000000), D4 := ((106190846999999903 : Rat) / 2048000000000000000), LB := ((21789369561331373 : Rat) / 100000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1399166200199999973 : Rat) / 512000000000000000), R := ((27984418754999999459 : Rat) / 10240000000000000000), D0 := ((27984418754999999459 : Rat) / 10240000000000000000), D1 := ((9373473730999999459 : Rat) / 10240000000000000000), D2 := ((1791164354999999459 : Rat) / 10240000000000000000), D3 := ((592260290999999459 : Rat) / 10240000000000000000), D4 := ((132464870999999879 : Rat) / 2560000000000000000), LB := ((567778234481231 : Rat) / 2500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27984418754999999459 : Rat) / 10240000000000000000), R := ((13992756752999999729 : Rat) / 5120000000000000000), D0 := ((13992756752999999729 : Rat) / 5120000000000000000), D1 := ((4687284240999999729 : Rat) / 5120000000000000000), D2 := ((896129552999999729 : Rat) / 5120000000000000000), D3 := ((296677520999999729 : Rat) / 5120000000000000000), D4 := ((528764732999999517 : Rat) / 10240000000000000000), LB := ((4747274316980743 : Rat) / 20000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13992756752999999729 : Rat) / 5120000000000000000), R := ((27986608256999999457 : Rat) / 10240000000000000000), D0 := ((27986608256999999457 : Rat) / 10240000000000000000), D1 := ((9375663232999999457 : Rat) / 10240000000000000000), D2 := ((1793353856999999457 : Rat) / 10240000000000000000), D3 := ((594449792999999457 : Rat) / 10240000000000000000), D4 := ((263834990999999759 : Rat) / 5120000000000000000), LB := ((38852347863539 : Rat) / 156250000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27986608256999999457 : Rat) / 10240000000000000000), R := ((874615718999999983 : Rat) / 320000000000000000), D0 := ((874615718999999983 : Rat) / 320000000000000000), D1 := ((293023686999999983 : Rat) / 320000000000000000), D2 := ((56076518999999983 : Rat) / 320000000000000000), D3 := ((18610766999999983 : Rat) / 320000000000000000), D4 := ((526575230999999519 : Rat) / 10240000000000000000), LB := ((521978630345421 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((874615718999999983 : Rat) / 320000000000000000), R := ((5597759551799999891 : Rat) / 2048000000000000000), D0 := ((5597759551799999891 : Rat) / 2048000000000000000), D1 := ((1875570546999999891 : Rat) / 2048000000000000000), D2 := ((359108671799999891 : Rat) / 2048000000000000000), D3 := ((119327858999999891 : Rat) / 2048000000000000000), D4 := ((3284252999999997 : Rat) / 64000000000000000), LB := ((2743706979446703 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5597759551799999891 : Rat) / 2048000000000000000), R := ((13994946254999999727 : Rat) / 5120000000000000000), D0 := ((13994946254999999727 : Rat) / 5120000000000000000), D1 := ((4689473742999999727 : Rat) / 5120000000000000000), D2 := ((898319054999999727 : Rat) / 5120000000000000000), D3 := ((298867022999999727 : Rat) / 5120000000000000000), D4 := ((524385728999999521 : Rat) / 10240000000000000000), LB := ((2888033160279857 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13994946254999999727 : Rat) / 5120000000000000000), R := ((27990987260999999453 : Rat) / 10240000000000000000), D0 := ((27990987260999999453 : Rat) / 10240000000000000000), D1 := ((9380042236999999453 : Rat) / 10240000000000000000), D2 := ((1797732860999999453 : Rat) / 10240000000000000000), D3 := ((598828796999999453 : Rat) / 10240000000000000000), D4 := ((261645488999999761 : Rat) / 5120000000000000000), LB := ((3042913368538347 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27990987260999999453 : Rat) / 10240000000000000000), R := ((6998020502999999863 : Rat) / 2560000000000000000), D0 := ((6998020502999999863 : Rat) / 2560000000000000000), D1 := ((2345284246999999863 : Rat) / 2560000000000000000), D2 := ((449706902999999863 : Rat) / 2560000000000000000), D3 := ((149980886999999863 : Rat) / 2560000000000000000), D4 := ((522196226999999523 : Rat) / 10240000000000000000), LB := ((1604194770553069 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6998020502999999863 : Rat) / 2560000000000000000), R := ((27993176762999999451 : Rat) / 10240000000000000000), D0 := ((27993176762999999451 : Rat) / 10240000000000000000), D1 := ((9382231738999999451 : Rat) / 10240000000000000000), D2 := ((1799922362999999451 : Rat) / 10240000000000000000), D3 := ((601018298999999451 : Rat) / 10240000000000000000), D4 := ((130275368999999881 : Rat) / 2560000000000000000), LB := ((16922519398310243 : Rat) / 50000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27993176762999999451 : Rat) / 10240000000000000000), R := ((559885430279999989 : Rat) / 204800000000000000), D0 := ((559885430279999989 : Rat) / 204800000000000000), D1 := ((187666529799999989 : Rat) / 204800000000000000), D2 := ((36020342279999989 : Rat) / 204800000000000000), D3 := ((12042260999999989 : Rat) / 204800000000000000), D4 := ((20800268999999981 : Rat) / 409600000000000000), LB := ((8928247132436451 : Rat) / 25000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((559885430279999989 : Rat) / 204800000000000000), R := ((27995366264999999449 : Rat) / 10240000000000000000), D0 := ((27995366264999999449 : Rat) / 10240000000000000000), D1 := ((9384421240999999449 : Rat) / 10240000000000000000), D2 := ((1802111864999999449 : Rat) / 10240000000000000000), D3 := ((603207800999999449 : Rat) / 10240000000000000000), D4 := ((259455986999999763 : Rat) / 5120000000000000000), LB := ((37688171990635233 : Rat) / 100000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27995366264999999449 : Rat) / 10240000000000000000), R := ((3499557626999999931 : Rat) / 1280000000000000000), D0 := ((3499557626999999931 : Rat) / 1280000000000000000), D1 := ((1173189498999999931 : Rat) / 1280000000000000000), D2 := ((225400826999999931 : Rat) / 1280000000000000000), D3 := ((75537818999999931 : Rat) / 1280000000000000000), D4 := ((517817222999999527 : Rat) / 10240000000000000000), LB := ((3977101927550297 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3499557626999999931 : Rat) / 1280000000000000000), R := ((27997555766999999447 : Rat) / 10240000000000000000), D0 := ((27997555766999999447 : Rat) / 10240000000000000000), D1 := ((9386610742999999447 : Rat) / 10240000000000000000), D2 := ((1804301366999999447 : Rat) / 10240000000000000000), D3 := ((605397302999999447 : Rat) / 10240000000000000000), D4 := ((64590308999999941 : Rat) / 1280000000000000000), LB := ((839239264372571 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27997555766999999447 : Rat) / 10240000000000000000), R := ((13999325258999999723 : Rat) / 5120000000000000000), D0 := ((13999325258999999723 : Rat) / 5120000000000000000), D1 := ((4693852746999999723 : Rat) / 5120000000000000000), D2 := ((902698058999999723 : Rat) / 5120000000000000000), D3 := ((303246026999999723 : Rat) / 5120000000000000000), D4 := ((515627720999999529 : Rat) / 10240000000000000000), LB := ((138316998177547 : Rat) / 312500000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13999325258999999723 : Rat) / 5120000000000000000), R := ((7000210004999999861 : Rat) / 2560000000000000000), D0 := ((7000210004999999861 : Rat) / 2560000000000000000), D1 := ((2347473748999999861 : Rat) / 2560000000000000000), D2 := ((451896404999999861 : Rat) / 2560000000000000000), D3 := ((152170388999999861 : Rat) / 2560000000000000000), D4 := ((51453296999999953 : Rat) / 1024000000000000000), LB := ((6040938453910627 : Rat) / 5000000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7000210004999999861 : Rat) / 2560000000000000000), R := ((14001514760999999721 : Rat) / 5120000000000000000), D0 := ((14001514760999999721 : Rat) / 5120000000000000000), D1 := ((4696042248999999721 : Rat) / 5120000000000000000), D2 := ((904887560999999721 : Rat) / 5120000000000000000), D3 := ((305435528999999721 : Rat) / 5120000000000000000), D4 := ((128085866999999883 : Rat) / 2560000000000000000), LB := ((2638319193126737 : Rat) / 50000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((14001514760999999721 : Rat) / 5120000000000000000), R := ((350065237799999993 : Rat) / 128000000000000000), D0 := ((350065237799999993 : Rat) / 128000000000000000), D1 := ((117428424999999993 : Rat) / 128000000000000000), D2 := ((22649557799999993 : Rat) / 128000000000000000), D3 := ((7663256999999993 : Rat) / 128000000000000000), D4 := ((255076982999999767 : Rat) / 5120000000000000000), LB := ((679604195875233 : Rat) / 6250000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((350065237799999993 : Rat) / 128000000000000000), R := ((14003704262999999719 : Rat) / 5120000000000000000), D0 := ((14003704262999999719 : Rat) / 5120000000000000000), D1 := ((4698231750999999719 : Rat) / 5120000000000000000), D2 := ((907077062999999719 : Rat) / 5120000000000000000), D3 := ((307625030999999719 : Rat) / 5120000000000000000), D4 := ((31747778999999971 : Rat) / 640000000000000000), LB := ((105721967469663 : Rat) / 625000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((14003704262999999719 : Rat) / 5120000000000000000), R := ((7002399506999999859 : Rat) / 2560000000000000000), D0 := ((7002399506999999859 : Rat) / 2560000000000000000), D1 := ((2349663250999999859 : Rat) / 2560000000000000000), D2 := ((454085906999999859 : Rat) / 2560000000000000000), D3 := ((154359890999999859 : Rat) / 2560000000000000000), D4 := ((252887480999999769 : Rat) / 5120000000000000000), LB := ((58514595149467 : Rat) / 250000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7002399506999999859 : Rat) / 2560000000000000000), R := ((14005893764999999717 : Rat) / 5120000000000000000), D0 := ((14005893764999999717 : Rat) / 5120000000000000000), D1 := ((4700421252999999717 : Rat) / 5120000000000000000), D2 := ((909266564999999717 : Rat) / 5120000000000000000), D3 := ((309814532999999717 : Rat) / 5120000000000000000), D4 := ((25179272999999977 : Rat) / 512000000000000000), LB := ((15174170669440823 : Rat) / 50000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((14005893764999999717 : Rat) / 5120000000000000000), R := ((3501747128999999929 : Rat) / 1280000000000000000), D0 := ((3501747128999999929 : Rat) / 1280000000000000000), D1 := ((1175379000999999929 : Rat) / 1280000000000000000), D2 := ((227590328999999929 : Rat) / 1280000000000000000), D3 := ((77727320999999929 : Rat) / 1280000000000000000), D4 := ((250697978999999771 : Rat) / 5120000000000000000), LB := ((7549355519169687 : Rat) / 20000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3501747128999999929 : Rat) / 1280000000000000000), R := ((2801616653399999943 : Rat) / 1024000000000000000), D0 := ((2801616653399999943 : Rat) / 1024000000000000000), D1 := ((940522150999999943 : Rat) / 1024000000000000000), D2 := ((182291213399999943 : Rat) / 1024000000000000000), D3 := ((62400806999999943 : Rat) / 1024000000000000000), D4 := ((62400806999999943 : Rat) / 1280000000000000000), LB := ((1824197967881247 : Rat) / 4000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2801616653399999943 : Rat) / 1024000000000000000), R := ((7004589008999999857 : Rat) / 2560000000000000000), D0 := ((7004589008999999857 : Rat) / 2560000000000000000), D1 := ((2351852752999999857 : Rat) / 2560000000000000000), D2 := ((456275408999999857 : Rat) / 2560000000000000000), D3 := ((156549392999999857 : Rat) / 2560000000000000000), D4 := ((248508476999999773 : Rat) / 5120000000000000000), LB := ((5392670877917283 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7004589008999999857 : Rat) / 2560000000000000000), R := ((14010272768999999713 : Rat) / 5120000000000000000), D0 := ((14010272768999999713 : Rat) / 5120000000000000000), D1 := ((4704800256999999713 : Rat) / 5120000000000000000), D2 := ((913645568999999713 : Rat) / 5120000000000000000), D3 := ((314193536999999713 : Rat) / 5120000000000000000), D4 := ((123706862999999887 : Rat) / 2560000000000000000), LB := ((6271596013810443 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((14010272768999999713 : Rat) / 5120000000000000000), R := ((437855234999999991 : Rat) / 160000000000000000), D0 := ((437855234999999991 : Rat) / 160000000000000000), D1 := ((147059218999999991 : Rat) / 160000000000000000), D2 := ((28585634999999991 : Rat) / 160000000000000000), D3 := ((9852758999999991 : Rat) / 160000000000000000), D4 := ((9852758999999991 : Rat) / 204800000000000000), LB := ((224927059798187 : Rat) / 312500000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((437855234999999991 : Rat) / 160000000000000000), R := ((14012462270999999711 : Rat) / 5120000000000000000), D0 := ((14012462270999999711 : Rat) / 5120000000000000000), D1 := ((4706989758999999711 : Rat) / 5120000000000000000), D2 := ((915835070999999711 : Rat) / 5120000000000000000), D3 := ((316383038999999711 : Rat) / 5120000000000000000), D4 := ((7663256999999993 : Rat) / 160000000000000000), LB := ((1634256292520453 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((14012462270999999711 : Rat) / 5120000000000000000), R := ((1401355702199999971 : Rat) / 512000000000000000), D0 := ((1401355702199999971 : Rat) / 512000000000000000), D1 := ((470808450999999971 : Rat) / 512000000000000000), D2 := ((91692982199999971 : Rat) / 512000000000000000), D3 := ((31747778999999971 : Rat) / 512000000000000000), D4 := ((244129472999999777 : Rat) / 5120000000000000000), LB := ((1149106117591947 : Rat) / 1250000000000000000) }
]

def block091RightChunk000L : Rat := ((22493622767857142867 : Rat) / 12500000000000000000)
def block091RightChunk000R : Rat := ((1401355702199999971 : Rat) / 512000000000000000)

def block091RightChunk000Certificate : Bool :=
  allBoxesValid block091RightChunk000 &&
  coversFromBool block091RightChunk000 block091RightChunk000L block091RightChunk000R

theorem block091RightChunk000Certificate_eq_true :
    block091RightChunk000Certificate = true := by
  native_decide

def block091RightChunk001 : List RatBox := [
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1401355702199999971 : Rat) / 512000000000000000), R := ((3503936630999999927 : Rat) / 1280000000000000000), D0 := ((3503936630999999927 : Rat) / 1280000000000000000), D1 := ((1177568502999999927 : Rat) / 1280000000000000000), D2 := ((229779830999999927 : Rat) / 1280000000000000000), D3 := ((79916822999999927 : Rat) / 1280000000000000000), D4 := ((121517360999999889 : Rat) / 2560000000000000000), LB := ((9810624505401933 : Rat) / 100000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3503936630999999927 : Rat) / 1280000000000000000), R := ((7008968012999999853 : Rat) / 2560000000000000000), D0 := ((7008968012999999853 : Rat) / 2560000000000000000), D1 := ((2356231756999999853 : Rat) / 2560000000000000000), D2 := ((460654412999999853 : Rat) / 2560000000000000000), D3 := ((160928396999999853 : Rat) / 2560000000000000000), D4 := ((12042260999999989 : Rat) / 256000000000000000), LB := ((12780324434589 : Rat) / 39062500000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7008968012999999853 : Rat) / 2560000000000000000), R := ((1752515690999999963 : Rat) / 640000000000000000), D0 := ((1752515690999999963 : Rat) / 640000000000000000), D1 := ((589331626999999963 : Rat) / 640000000000000000), D2 := ((115437290999999963 : Rat) / 640000000000000000), D3 := ((40505786999999963 : Rat) / 640000000000000000), D4 := ((119327858999999891 : Rat) / 2560000000000000000), LB := ((5760997702879411 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1752515690999999963 : Rat) / 640000000000000000), R := ((7011157514999999851 : Rat) / 2560000000000000000), D0 := ((7011157514999999851 : Rat) / 2560000000000000000), D1 := ((2358421258999999851 : Rat) / 2560000000000000000), D2 := ((462843914999999851 : Rat) / 2560000000000000000), D3 := ((163117898999999851 : Rat) / 2560000000000000000), D4 := ((29558276999999973 : Rat) / 640000000000000000), LB := ((1690453731251207 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7011157514999999851 : Rat) / 2560000000000000000), R := ((140245045319999997 : Rat) / 51200000000000000), D0 := ((140245045319999997 : Rat) / 51200000000000000), D1 := ((47190320199999997 : Rat) / 51200000000000000), D2 := ((9278773319999997 : Rat) / 51200000000000000), D3 := ((3284252999999997 : Rat) / 51200000000000000), D4 := ((117138356999999893 : Rat) / 2560000000000000000), LB := ((11349176135511119 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((140245045319999997 : Rat) / 51200000000000000), R := ((7013347016999999849 : Rat) / 2560000000000000000), D0 := ((7013347016999999849 : Rat) / 2560000000000000000), D1 := ((2360610760999999849 : Rat) / 2560000000000000000), D2 := ((465033416999999849 : Rat) / 2560000000000000000), D3 := ((165307400999999849 : Rat) / 2560000000000000000), D4 := ((58021802999999947 : Rat) / 1280000000000000000), LB := ((3613855499238483 : Rat) / 2500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7013347016999999849 : Rat) / 2560000000000000000), R := ((876805220999999981 : Rat) / 320000000000000000), D0 := ((876805220999999981 : Rat) / 320000000000000000), D1 := ((295213188999999981 : Rat) / 320000000000000000), D2 := ((58266020999999981 : Rat) / 320000000000000000), D3 := ((20800268999999981 : Rat) / 320000000000000000), D4 := ((22989770999999979 : Rat) / 512000000000000000), LB := ((8887406793153807 : Rat) / 5000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((876805220999999981 : Rat) / 320000000000000000), R := ((3508315634999999923 : Rat) / 1280000000000000000), D0 := ((3508315634999999923 : Rat) / 1280000000000000000), D1 := ((1181947506999999923 : Rat) / 1280000000000000000), D2 := ((234158834999999923 : Rat) / 1280000000000000000), D3 := ((84295826999999923 : Rat) / 1280000000000000000), D4 := ((14231762999999987 : Rat) / 320000000000000000), LB := ((562150995750077 : Rat) / 2000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3508315634999999923 : Rat) / 1280000000000000000), R := ((1754705192999999961 : Rat) / 640000000000000000), D0 := ((1754705192999999961 : Rat) / 640000000000000000), D1 := ((591521128999999961 : Rat) / 640000000000000000), D2 := ((117626792999999961 : Rat) / 640000000000000000), D3 := ((42695288999999961 : Rat) / 640000000000000000), D4 := ((55832300999999949 : Rat) / 1280000000000000000), LB := ((10567258212267339 : Rat) / 10000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1754705192999999961 : Rat) / 640000000000000000), R := ((3510505136999999921 : Rat) / 1280000000000000000), D0 := ((3510505136999999921 : Rat) / 1280000000000000000), D1 := ((1184137008999999921 : Rat) / 1280000000000000000), D2 := ((236348336999999921 : Rat) / 1280000000000000000), D3 := ((86485328999999921 : Rat) / 1280000000000000000), D4 := ((1094750999999999 : Rat) / 25600000000000000), LB := ((481047872498197 : Rat) / 250000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3510505136999999921 : Rat) / 1280000000000000000), R := ((43894998599999999 : Rat) / 16000000000000000), D0 := ((43894998599999999 : Rat) / 16000000000000000), D1 := ((14815396999999999 : Rat) / 16000000000000000), D2 := ((2968038599999999 : Rat) / 16000000000000000), D3 := ((1094750999999999 : Rat) / 16000000000000000), D4 := ((53642798999999951 : Rat) / 1280000000000000000), LB := ((7217615663787369 : Rat) / 2500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43894998599999999 : Rat) / 16000000000000000), R := ((1756894694999999959 : Rat) / 640000000000000000), D0 := ((1756894694999999959 : Rat) / 640000000000000000), D1 := ((593710630999999959 : Rat) / 640000000000000000), D2 := ((119816294999999959 : Rat) / 640000000000000000), D3 := ((44884790999999959 : Rat) / 640000000000000000), D4 := ((3284252999999997 : Rat) / 80000000000000000), LB := ((26428857756843893 : Rat) / 100000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1756894694999999959 : Rat) / 640000000000000000), R := ((878994722999999979 : Rat) / 320000000000000000), D0 := ((878994722999999979 : Rat) / 320000000000000000), D1 := ((297402690999999979 : Rat) / 320000000000000000), D2 := ((60455522999999979 : Rat) / 320000000000000000), D3 := ((22989770999999979 : Rat) / 320000000000000000), D4 := ((25179272999999977 : Rat) / 640000000000000000), LB := ((2708727307837777 : Rat) / 1000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((878994722999999979 : Rat) / 320000000000000000), R := ((1759084196999999957 : Rat) / 640000000000000000), D0 := ((1759084196999999957 : Rat) / 640000000000000000), D1 := ((595900132999999957 : Rat) / 640000000000000000), D2 := ((122005796999999957 : Rat) / 640000000000000000), D3 := ((47074292999999957 : Rat) / 640000000000000000), D4 := ((12042260999999989 : Rat) / 320000000000000000), LB := ((2800917326053809 : Rat) / 500000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1759084196999999957 : Rat) / 640000000000000000), R := ((440044736999999989 : Rat) / 160000000000000000), D0 := ((440044736999999989 : Rat) / 160000000000000000), D1 := ((149248720999999989 : Rat) / 160000000000000000), D2 := ((30775136999999989 : Rat) / 160000000000000000), D3 := ((12042260999999989 : Rat) / 160000000000000000), D4 := ((22989770999999979 : Rat) / 640000000000000000), LB := ((2246033446466983 : Rat) / 250000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((440044736999999989 : Rat) / 160000000000000000), R := ((881184224999999977 : Rat) / 320000000000000000), D0 := ((881184224999999977 : Rat) / 320000000000000000), D1 := ((299592192999999977 : Rat) / 320000000000000000), D2 := ((62645024999999977 : Rat) / 320000000000000000), D3 := ((25179272999999977 : Rat) / 320000000000000000), D4 := ((1094750999999999 : Rat) / 32000000000000000), LB := ((349558526251563 : Rat) / 62500000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((881184224999999977 : Rat) / 320000000000000000), R := ((110284871999999997 : Rat) / 40000000000000000), D0 := ((110284871999999997 : Rat) / 40000000000000000), D1 := ((37585867999999997 : Rat) / 40000000000000000), D2 := ((7967471999999997 : Rat) / 40000000000000000), D3 := ((3284252999999997 : Rat) / 40000000000000000), D4 := ((9852758999999991 : Rat) / 320000000000000000), LB := ((1528417693648687 : Rat) / 100000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((110284871999999997 : Rat) / 40000000000000000), R := ((442234238999999987 : Rat) / 160000000000000000), D0 := ((442234238999999987 : Rat) / 160000000000000000), D1 := ((151438222999999987 : Rat) / 160000000000000000), D2 := ((32964638999999987 : Rat) / 160000000000000000), D3 := ((14231762999999987 : Rat) / 160000000000000000), D4 := ((1094750999999999 : Rat) / 40000000000000000), LB := ((13406306575283411 : Rat) / 1000000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((442234238999999987 : Rat) / 160000000000000000), R := ((221664494999999993 : Rat) / 80000000000000000), D0 := ((221664494999999993 : Rat) / 80000000000000000), D1 := ((76266486999999993 : Rat) / 80000000000000000), D2 := ((17029694999999993 : Rat) / 80000000000000000), D3 := ((7663256999999993 : Rat) / 80000000000000000), D4 := ((3284252999999997 : Rat) / 160000000000000000), LB := ((10173019937324379 : Rat) / 200000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((221664494999999993 : Rat) / 80000000000000000), R := ((27844905749999999 : Rat) / 10000000000000000), D0 := ((27844905749999999 : Rat) / 10000000000000000), D1 := ((9670154749999999 : Rat) / 10000000000000000), D2 := ((2265555749999999 : Rat) / 10000000000000000), D3 := ((1094750999999999 : Rat) / 10000000000000000), D4 := ((1094750999999999 : Rat) / 80000000000000000), LB := ((4360865209527859 : Rat) / 50000000000000000) },
  { w1 := ((1462816853022853 : Rat) / 400000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1151845655797093 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27844905749999999 : Rat) / 10000000000000000), R := ((139984265625000000039 : Rat) / 50000000000000000000), D0 := ((139984265625000000039 : Rat) / 50000000000000000000), D1 := ((49110510625000000039 : Rat) / 50000000000000000000), D2 := ((12087515625000000039 : Rat) / 50000000000000000000), D3 := ((6233491875000000039 : Rat) / 50000000000000000000), D4 := ((759736875000005039 : Rat) / 50000000000000000000), LB := ((322495563725933 : Rat) / 500000000000000000) }
]

def block091RightChunk001L : Rat := ((1401355702199999971 : Rat) / 512000000000000000)
def block091RightChunk001R : Rat := ((139984265625000000039 : Rat) / 50000000000000000000)

def block091RightChunk001Certificate : Bool :=
  allBoxesValid block091RightChunk001 &&
  coversFromBool block091RightChunk001 block091RightChunk001L block091RightChunk001R

theorem block091RightChunk001Certificate_eq_true :
    block091RightChunk001Certificate = true := by
  native_decide

def block091RightChainCertificate : Bool :=
  decide (
    block091RightL = ((22493622767857142867 : Rat) / 12500000000000000000) /\
    ((1401355702199999971 : Rat) / 512000000000000000) = ((1401355702199999971 : Rat) / 512000000000000000) /\
    ((139984265625000000039 : Rat) / 50000000000000000000) = block091RightR)

theorem block091RightChainCertificate_eq_true :
    block091RightChainCertificate = true := by
  native_decide

def block091LeftBoxCount : Nat := boxCount block091LeftBoxes
def block091RightBoxCount : Nat := 121

def block091_rational_certificate : Prop :=
    block091LeftCertificate = true /\
    block091RightChainCertificate = true /\
    block091RightChunk000Certificate = true /\
    block091RightChunk001Certificate = true

theorem block091_rational_certificate_proof :
    block091_rational_certificate := by
  exact ⟨block091LeftCertificate_eq_true, block091RightChainCertificate_eq_true, block091RightChunk000Certificate_eq_true, block091RightChunk001Certificate_eq_true⟩

end Block091
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block091

open Set

def block091W1 : Rat := ((1462816853022853 : Rat) / 400000000000000)
def block091W2 : Rat := (0 : Rat)
def block091W3 : Rat := (0 : Rat)
def block091W4 : Rat := ((1151845655797093 : Rat) / 5000000000000000)
def block091S1 : Rat := ((18174751 : Rat) / 10000000)
def block091S2 : Rat := ((511587 : Rat) / 200000)
def block091S3 : Rat := ((107000619 : Rat) / 40000000)
def block091S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block091V (y : ℝ) : ℝ :=
  ratPotential block091W1 block091W2 block091W3 block091W4 block091S1 block091S2 block091S3 block091S4 y

def block091LeftParamsCertificate : Bool :=
  allBoxesSameParams block091LeftBoxes block091W1 block091W2 block091W3 block091W4 block091S1 block091S2 block091S3 block091S4

theorem block091LeftParamsCertificate_eq_true :
    block091LeftParamsCertificate = true := by
  native_decide

theorem block091_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block091LeftL : ℝ) (block091LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block091S1 : ℝ))
    (hy2ne : y ≠ (block091S2 : ℝ))
    (hy3ne : y ≠ (block091S3 : ℝ))
    (hy4ne : y ≠ (block091S4 : ℝ)) :
    0 < block091V y := by
  have hcert := block091LeftCertificate_eq_true
  unfold block091LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block091LeftBoxes) (lo := block091LeftL) (hi := block091LeftR)
    (w1 := block091W1) (w2 := block091W2) (w3 := block091W3) (w4 := block091W4)
    (s1 := block091S1) (s2 := block091S2) (s3 := block091S3) (s4 := block091S4)
    hboxes hcover block091LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block091RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block091RightChunk000 block091W1 block091W2 block091W3 block091W4 block091S1 block091S2 block091S3 block091S4

theorem block091RightChunk000ParamsCertificate_eq_true :
    block091RightChunk000ParamsCertificate = true := by
  native_decide

theorem block091_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block091RightChunk000L : ℝ) (block091RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block091S1 : ℝ))
    (hy2ne : y ≠ (block091S2 : ℝ))
    (hy3ne : y ≠ (block091S3 : ℝ))
    (hy4ne : y ≠ (block091S4 : ℝ)) :
    0 < block091V y := by
  have hcert := block091RightChunk000Certificate_eq_true
  unfold block091RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block091RightChunk000) (lo := block091RightChunk000L) (hi := block091RightChunk000R)
    (w1 := block091W1) (w2 := block091W2) (w3 := block091W3) (w4 := block091W4)
    (s1 := block091S1) (s2 := block091S2) (s3 := block091S3) (s4 := block091S4)
    hboxes hcover block091RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block091RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block091RightChunk001 block091W1 block091W2 block091W3 block091W4 block091S1 block091S2 block091S3 block091S4

theorem block091RightChunk001ParamsCertificate_eq_true :
    block091RightChunk001ParamsCertificate = true := by
  native_decide

theorem block091_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block091RightChunk001L : ℝ) (block091RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block091S1 : ℝ))
    (hy2ne : y ≠ (block091S2 : ℝ))
    (hy3ne : y ≠ (block091S3 : ℝ))
    (hy4ne : y ≠ (block091S4 : ℝ)) :
    0 < block091V y := by
  have hcert := block091RightChunk001Certificate_eq_true
  unfold block091RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block091RightChunk001) (lo := block091RightChunk001L) (hi := block091RightChunk001R)
    (w1 := block091W1) (w2 := block091W2) (w3 := block091W3) (w4 := block091W4)
    (s1 := block091S1) (s2 := block091S2) (s3 := block091S3) (s4 := block091S4)
    hboxes hcover block091RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block091_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block091RightL : ℝ) (block091RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block091S1 : ℝ))
    (hy2ne : y ≠ (block091S2 : ℝ))
    (hy3ne : y ≠ (block091S3 : ℝ))
    (hy4ne : y ≠ (block091S4 : ℝ)) :
    0 < block091V y := by
  by_cases h0 : y ≤ (block091RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block091RightChunk000L : ℝ) (block091RightChunk000R : ℝ) := by
      have hL : (block091RightChunk000L : ℝ) = (block091RightL : ℝ) := by
        norm_num [block091RightChunk000L, block091RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block091_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block091RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block091RightChunk001L : ℝ) = (block091RightChunk000R : ℝ) := by
      norm_num [block091RightChunk001L, block091RightChunk000R]
    have hR : (block091RightChunk001R : ℝ) = (block091RightR : ℝ) := by
      norm_num [block091RightChunk001R, block091RightR]
    have hyc : y ∈ Icc (block091RightChunk001L : ℝ) (block091RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block091_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block091_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block091LeftL : ℝ) (block091LeftR : ℝ) →
    y ≠ 0 → y ≠ (block091S1 : ℝ) → y ≠ (block091S2 : ℝ) →
    y ≠ (block091S3 : ℝ) → y ≠ (block091S4 : ℝ) → 0 < block091V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block091RightL : ℝ) (block091RightR : ℝ) →
    y ≠ 0 → y ≠ (block091S1 : ℝ) → y ≠ (block091S2 : ℝ) →
    y ≠ (block091S3 : ℝ) → y ≠ (block091S4 : ℝ) → 0 < block091V y)

theorem block091_reallog_certificate_proof :
    block091_reallog_certificate := by
  exact ⟨block091_left_V_pos, block091_right_V_pos⟩

end Block091
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block091.block091V
#check Erdos1038Lean.M1817475.Block091.block091_left_V_pos
#check Erdos1038Lean.M1817475.Block091.block091_right_V_pos
#check Erdos1038Lean.M1817475.Block091.block091_reallog_certificate_proof
