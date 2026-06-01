/-
Self-contained Lean4Web paste file.
Block 266 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block266

def block266LeftL : Rat := ((38263944196428571543 : Rat) / 50000000000000000000)
def block266LeftR : Rat := ((19136859375000000057 : Rat) / 25000000000000000000)
def block266RightL : Rat := ((88263944196428571543 : Rat) / 50000000000000000000)
def block266RightR : Rat := ((69136859375000000057 : Rat) / 25000000000000000000)

def block266LeftBoxes : List RatBox := [
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((38263944196428571543 : Rat) / 50000000000000000000), R := ((19136859375000000057 : Rat) / 25000000000000000000), D0 := ((19136859375000000057 : Rat) / 25000000000000000000), D1 := ((52609810803571428457 : Rat) / 50000000000000000000), D2 := ((89632805803571428457 : Rat) / 50000000000000000000), D3 := ((48891924821428571321 : Rat) / 25000000000000000000), D4 := ((101566606874999994859 : Rat) / 50000000000000000000), LB := ((3070773935995863 : Rat) / 5000000000000000000) }
]

def block266LeftCertificate : Bool :=
  allBoxesValid block266LeftBoxes &&
  coversFromBool block266LeftBoxes block266LeftL block266LeftR

theorem block266LeftCertificate_eq_true :
    block266LeftCertificate = true := by
  native_decide

def block266RightChunk000 : List RatBox := [
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((88263944196428571543 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((2609810803571428457 : Rat) / 50000000000000000000), D2 := ((39632805803571428457 : Rat) / 50000000000000000000), D3 := ((23891924821428571321 : Rat) / 25000000000000000000), D4 := ((51566606874999994859 : Rat) / 50000000000000000000), LB := ((2460264170958637 : Rat) / 1000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((24478398035714283201 : Rat) / 25000000000000000000), LB := ((867780443458273 : Rat) / 3125000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((15222649285714283201 : Rat) / 25000000000000000000), LB := ((18154886836587517 : Rat) / 100000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((4406933392857142837 : Rat) / 10000000000000000000), D4 := ((12908712098214283201 : Rat) / 25000000000000000000), LB := ((1842459647081801 : Rat) / 100000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((10594774910714283201 : Rat) / 25000000000000000000), LB := ((4753187685611293 : Rat) / 100000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((3249964799107142837 : Rat) / 10000000000000000000), D4 := ((10016290613839283201 : Rat) / 25000000000000000000), LB := ((673796036923021 : Rat) / 31250000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((3018571080357142837 : Rat) / 10000000000000000000), D4 := ((9437806316964283201 : Rat) / 25000000000000000000), LB := ((2325325179669513 : Rat) / 100000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2902874220982142837 : Rat) / 10000000000000000000), D4 := ((9148564168526783201 : Rat) / 25000000000000000000), LB := ((528483319075721 : Rat) / 40000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2787177361607142837 : Rat) / 10000000000000000000), D4 := ((8859322020089283201 : Rat) / 25000000000000000000), LB := ((21218282227642993 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2671480502232142837 : Rat) / 10000000000000000000), D4 := ((8570079871651783201 : Rat) / 25000000000000000000), LB := ((3999769254922819 : Rat) / 500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2613632072544642837 : Rat) / 10000000000000000000), D4 := ((8425458797433033201 : Rat) / 25000000000000000000), LB := ((356917767909537 : Rat) / 80000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((8280837723214283201 : Rat) / 25000000000000000000), LB := ((312695476172381 : Rat) / 250000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((2497935213169642837 : Rat) / 10000000000000000000), D4 := ((8136216648995533201 : Rat) / 25000000000000000000), LB := ((2037878219020739 : Rat) / 500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((2469010998325892837 : Rat) / 10000000000000000000), D4 := ((8063906111886158201 : Rat) / 25000000000000000000), LB := ((2757221065879001 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((2440086783482142837 : Rat) / 10000000000000000000), D4 := ((7991595574776783201 : Rat) / 25000000000000000000), LB := ((1533019497773791 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((2411162568638392837 : Rat) / 10000000000000000000), D4 := ((7919285037667408201 : Rat) / 25000000000000000000), LB := ((2031577776079041 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((12718992651 : Rat) / 5120000000), D0 := ((12718992651 : Rat) / 5120000000), D1 := ((3413520139 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((2382238353794642837 : Rat) / 10000000000000000000), D4 := ((7846974500558033201 : Rat) / 25000000000000000000), LB := ((5479868041649849 : Rat) / 2500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12718992651 : Rat) / 5120000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((377634549 : Rat) / 5120000000), D3 := ((2367776246372767837 : Rat) / 10000000000000000000), D4 := ((7810819232003345701 : Rat) / 25000000000000000000), LB := ((8564807276459363 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((12733801849 : Rat) / 5120000000), D0 := ((12733801849 : Rat) / 5120000000), D1 := ((3428329337 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((2353314138950892837 : Rat) / 10000000000000000000), D4 := ((7774663963448658201 : Rat) / 25000000000000000000), LB := ((6303505466400683 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12733801849 : Rat) / 5120000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((362825351 : Rat) / 5120000000), D3 := ((2338852031529017837 : Rat) / 10000000000000000000), D4 := ((7738508694893970701 : Rat) / 25000000000000000000), LB := ((8357066934963631 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((12748611047 : Rat) / 5120000000), D0 := ((12748611047 : Rat) / 5120000000), D1 := ((688627707 : Rat) / 1024000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((2324389924107142837 : Rat) / 10000000000000000000), D4 := ((7702353426339283201 : Rat) / 25000000000000000000), LB := ((10963695605097079 : Rat) / 25000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12748611047 : Rat) / 5120000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((348016153 : Rat) / 5120000000), D3 := ((2309927816685267837 : Rat) / 10000000000000000000), D4 := ((7666198157784595701 : Rat) / 25000000000000000000), LB := ((1745633489297349 : Rat) / 25000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((25519435891 : Rat) / 10240000000), D0 := ((25519435891 : Rat) / 10240000000), D1 := ((6908490867 : Rat) / 10240000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((2295465709263392837 : Rat) / 10000000000000000000), D4 := ((7630042889229908201 : Rat) / 25000000000000000000), LB := ((5612166448459577 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25519435891 : Rat) / 10240000000), R := ((2552684049 : Rat) / 1024000000), D0 := ((2552684049 : Rat) / 1024000000), D1 := ((3457947733 : Rat) / 5120000000), D2 := ((673818509 : Rat) / 10240000000), D3 := ((2288234655552455337 : Rat) / 10000000000000000000), D4 := ((7611965254952564451 : Rat) / 25000000000000000000), LB := ((962453931300733 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((2552684049 : Rat) / 1024000000), R := ((25534245089 : Rat) / 10240000000), D0 := ((25534245089 : Rat) / 10240000000), D1 := ((1384660013 : Rat) / 2048000000), D2 := ((66641391 : Rat) / 1024000000), D3 := ((2281003601841517837 : Rat) / 10000000000000000000), D4 := ((7593887620675220701 : Rat) / 25000000000000000000), LB := ((8099996520873343 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25534245089 : Rat) / 10240000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((659009311 : Rat) / 10240000000), D3 := ((2273772548130580337 : Rat) / 10000000000000000000), D4 := ((7575809986397876951 : Rat) / 25000000000000000000), LB := ((3325802895897123 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((25549054287 : Rat) / 10240000000), D0 := ((25549054287 : Rat) / 10240000000), D1 := ((6938109263 : Rat) / 10240000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((2266541494419642837 : Rat) / 10000000000000000000), D4 := ((7557732352120533201 : Rat) / 25000000000000000000), LB := ((5280295338137009 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25549054287 : Rat) / 10240000000), R := ((12778229443 : Rat) / 5120000000), D0 := ((12778229443 : Rat) / 5120000000), D1 := ((3472756931 : Rat) / 5120000000), D2 := ((644200113 : Rat) / 10240000000), D3 := ((2259310440708705337 : Rat) / 10000000000000000000), D4 := ((7539654717843189451 : Rat) / 25000000000000000000), LB := ((39870214819442973 : Rat) / 100000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12778229443 : Rat) / 5120000000), R := ((5112772697 : Rat) / 2048000000), D0 := ((5112772697 : Rat) / 2048000000), D1 := ((6952918461 : Rat) / 10240000000), D2 := ((318397757 : Rat) / 5120000000), D3 := ((2252079386997767837 : Rat) / 10000000000000000000), D4 := ((7521577083565845701 : Rat) / 25000000000000000000), LB := ((2772769890165283 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((5112772697 : Rat) / 2048000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((125878183 : Rat) / 2048000000), D3 := ((2244848333286830337 : Rat) / 10000000000000000000), D4 := ((7503499449288501951 : Rat) / 25000000000000000000), LB := ((1638556881147779 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((25578672683 : Rat) / 10240000000), D0 := ((25578672683 : Rat) / 10240000000), D1 := ((6967727659 : Rat) / 10240000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((2237617279575892837 : Rat) / 10000000000000000000), D4 := ((7485421815011158201 : Rat) / 25000000000000000000), LB := ((1170861614818719 : Rat) / 20000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25578672683 : Rat) / 10240000000), R := ((10232949993 : Rat) / 4096000000), D0 := ((10232949993 : Rat) / 4096000000), D1 := ((13942859917 : Rat) / 20480000000), D2 := ((614581717 : Rat) / 10240000000), D3 := ((2230386225864955337 : Rat) / 10000000000000000000), D4 := ((7467344180733814451 : Rat) / 25000000000000000000), LB := ((815503866985201 : Rat) / 1250000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((10232949993 : Rat) / 4096000000), R := ((12793038641 : Rat) / 5120000000), D0 := ((12793038641 : Rat) / 5120000000), D1 := ((3487566129 : Rat) / 5120000000), D2 := ((244351767 : Rat) / 4096000000), D3 := ((2226770699009486587 : Rat) / 10000000000000000000), D4 := ((466144085224696411 : Rat) / 1562500000000000000), LB := ((6066605202375563 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12793038641 : Rat) / 5120000000), R := ((51179559163 : Rat) / 20480000000), D0 := ((51179559163 : Rat) / 20480000000), D1 := ((2791533823 : Rat) / 4096000000), D2 := ((303588559 : Rat) / 5120000000), D3 := ((2223155172154017837 : Rat) / 10000000000000000000), D4 := ((7449266546456470701 : Rat) / 25000000000000000000), LB := ((5630146466186203 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51179559163 : Rat) / 20480000000), R := ((25593481881 : Rat) / 10240000000), D0 := ((25593481881 : Rat) / 10240000000), D1 := ((6982536857 : Rat) / 10240000000), D2 := ((1206949637 : Rat) / 20480000000), D3 := ((2219539645298549087 : Rat) / 10000000000000000000), D4 := ((3720113864658899413 : Rat) / 12500000000000000000), LB := ((5214800082028459 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25593481881 : Rat) / 10240000000), R := ((51194368361 : Rat) / 20480000000), D0 := ((51194368361 : Rat) / 20480000000), D1 := ((13972478313 : Rat) / 20480000000), D2 := ((599772519 : Rat) / 10240000000), D3 := ((2215924118443080337 : Rat) / 10000000000000000000), D4 := ((7431188912179126951 : Rat) / 25000000000000000000), LB := ((24103569032898897 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51194368361 : Rat) / 20480000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((1192140439 : Rat) / 20480000000), D3 := ((2212308591587611587 : Rat) / 10000000000000000000), D4 := ((1855537523760113769 : Rat) / 6250000000000000000), LB := ((8896075711209983 : Rat) / 20000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((51209177559 : Rat) / 20480000000), D0 := ((51209177559 : Rat) / 20480000000), D1 := ((13987287511 : Rat) / 20480000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((2208693064732142837 : Rat) / 10000000000000000000), D4 := ((7413111277901783201 : Rat) / 25000000000000000000), LB := ((10242312407014731 : Rat) / 25000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51209177559 : Rat) / 20480000000), R := ((25608291079 : Rat) / 10240000000), D0 := ((25608291079 : Rat) / 10240000000), D1 := ((1399469211 : Rat) / 2048000000), D2 := ((1177331241 : Rat) / 20480000000), D3 := ((2205077537876674087 : Rat) / 10000000000000000000), D4 := ((3702036230381555663 : Rat) / 12500000000000000000), LB := ((18837652202458033 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25608291079 : Rat) / 10240000000), R := ((51223986757 : Rat) / 20480000000), D0 := ((51223986757 : Rat) / 20480000000), D1 := ((14002096709 : Rat) / 20480000000), D2 := ((584963321 : Rat) / 10240000000), D3 := ((2201462011021205337 : Rat) / 10000000000000000000), D4 := ((7395033643624439451 : Rat) / 25000000000000000000), LB := ((6757836410519 : Rat) / 19531250000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51223986757 : Rat) / 20480000000), R := ((12807847839 : Rat) / 5120000000), D0 := ((12807847839 : Rat) / 5120000000), D1 := ((3502375327 : Rat) / 5120000000), D2 := ((1162522043 : Rat) / 20480000000), D3 := ((2197846484165736587 : Rat) / 10000000000000000000), D4 := ((923249353310720947 : Rat) / 3125000000000000000), LB := ((3174531027152483 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12807847839 : Rat) / 5120000000), R := ((10247759191 : Rat) / 4096000000), D0 := ((10247759191 : Rat) / 4096000000), D1 := ((14016905907 : Rat) / 20480000000), D2 := ((288779361 : Rat) / 5120000000), D3 := ((2194230957310267837 : Rat) / 10000000000000000000), D4 := ((7376956009347095701 : Rat) / 25000000000000000000), LB := ((14556251134933973 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((10247759191 : Rat) / 4096000000), R := ((25623100277 : Rat) / 10240000000), D0 := ((25623100277 : Rat) / 10240000000), D1 := ((7012155253 : Rat) / 10240000000), D2 := ((229542569 : Rat) / 4096000000), D3 := ((2190615430454799087 : Rat) / 10000000000000000000), D4 := ((3683958596104211913 : Rat) / 12500000000000000000), LB := ((26703361143348703 : Rat) / 100000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25623100277 : Rat) / 10240000000), R := ((51253605153 : Rat) / 20480000000), D0 := ((51253605153 : Rat) / 20480000000), D1 := ((2806343021 : Rat) / 4096000000), D2 := ((570154123 : Rat) / 10240000000), D3 := ((2186999903599330337 : Rat) / 10000000000000000000), D4 := ((7358878375069751951 : Rat) / 25000000000000000000), LB := ((24519578738185777 : Rat) / 100000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51253605153 : Rat) / 20480000000), R := ((6407626219 : Rat) / 2560000000), D0 := ((6407626219 : Rat) / 2560000000), D1 := ((1754889963 : Rat) / 2560000000), D2 := ((1132903647 : Rat) / 20480000000), D3 := ((2183384376743861587 : Rat) / 10000000000000000000), D4 := ((1837459889482770019 : Rat) / 6250000000000000000), LB := ((282035959403501 : Rat) / 1250000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6407626219 : Rat) / 2560000000), R := ((51268414351 : Rat) / 20480000000), D0 := ((51268414351 : Rat) / 20480000000), D1 := ((14046524303 : Rat) / 20480000000), D2 := ((140687381 : Rat) / 2560000000), D3 := ((2179768849888392837 : Rat) / 10000000000000000000), D4 := ((7340800740792408201 : Rat) / 25000000000000000000), LB := ((10417503745427381 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51268414351 : Rat) / 20480000000), R := ((1025516379 : Rat) / 409600000), D0 := ((1025516379 : Rat) / 409600000), D1 := ((7026964451 : Rat) / 10240000000), D2 := ((1118094449 : Rat) / 20480000000), D3 := ((2176153323032924087 : Rat) / 10000000000000000000), D4 := ((3665880961826868163 : Rat) / 12500000000000000000), LB := ((3867550929508301 : Rat) / 20000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1025516379 : Rat) / 409600000), R := ((51283223549 : Rat) / 20480000000), D0 := ((51283223549 : Rat) / 20480000000), D1 := ((14061333501 : Rat) / 20480000000), D2 := ((22213797 : Rat) / 409600000), D3 := ((2172537796177455337 : Rat) / 10000000000000000000), D4 := ((7322723106515064451 : Rat) / 25000000000000000000), LB := ((3614586822026089 : Rat) / 20000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51283223549 : Rat) / 20480000000), R := ((12822657037 : Rat) / 5120000000), D0 := ((12822657037 : Rat) / 5120000000), D1 := ((140687381 : Rat) / 204800000), D2 := ((1103285251 : Rat) / 20480000000), D3 := ((2168922269321986587 : Rat) / 10000000000000000000), D4 := ((57138158510753067 : Rat) / 195312500000000000), LB := ((17042394794014593 : Rat) / 100000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12822657037 : Rat) / 5120000000), R := ((51298032747 : Rat) / 20480000000), D0 := ((51298032747 : Rat) / 20480000000), D1 := ((14076142699 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 5120000000), D3 := ((2165306742466517837 : Rat) / 10000000000000000000), D4 := ((7304645472237720701 : Rat) / 25000000000000000000), LB := ((8124009751450667 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51298032747 : Rat) / 20480000000), R := ((25652718673 : Rat) / 10240000000), D0 := ((25652718673 : Rat) / 10240000000), D1 := ((7041773649 : Rat) / 10240000000), D2 := ((1088476053 : Rat) / 20480000000), D3 := ((2161691215611049087 : Rat) / 10000000000000000000), D4 := ((3647803327549524413 : Rat) / 12500000000000000000), LB := ((15691725818500757 : Rat) / 100000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25652718673 : Rat) / 10240000000), R := ((10262568389 : Rat) / 4096000000), D0 := ((10262568389 : Rat) / 4096000000), D1 := ((14090951897 : Rat) / 20480000000), D2 := ((540535727 : Rat) / 10240000000), D3 := ((2158075688755580337 : Rat) / 10000000000000000000), D4 := ((7286567837960376951 : Rat) / 25000000000000000000), LB := ((7687733510378103 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((10262568389 : Rat) / 4096000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((214733371 : Rat) / 4096000000), D3 := ((2154460161900111587 : Rat) / 10000000000000000000), D4 := ((1819382255205426269 : Rat) / 6250000000000000000), LB := ((1912654129876401 : Rat) / 12500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((51327651143 : Rat) / 20480000000), D0 := ((51327651143 : Rat) / 20480000000), D1 := ((2821152219 : Rat) / 4096000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((2150844635044642837 : Rat) / 10000000000000000000), D4 := ((7268490203683033201 : Rat) / 25000000000000000000), LB := ((7735525718025049 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51327651143 : Rat) / 20480000000), R := ((25667527871 : Rat) / 10240000000), D0 := ((25667527871 : Rat) / 10240000000), D1 := ((7056582847 : Rat) / 10240000000), D2 := ((1058857657 : Rat) / 20480000000), D3 := ((2147229108189174087 : Rat) / 10000000000000000000), D4 := ((3629725693272180663 : Rat) / 12500000000000000000), LB := ((3177397685246719 : Rat) / 20000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25667527871 : Rat) / 10240000000), R := ((51342460341 : Rat) / 20480000000), D0 := ((51342460341 : Rat) / 20480000000), D1 := ((14120570293 : Rat) / 20480000000), D2 := ((525726529 : Rat) / 10240000000), D3 := ((2143613581333705337 : Rat) / 10000000000000000000), D4 := ((7250412569405689451 : Rat) / 25000000000000000000), LB := ((8275574964564103 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51342460341 : Rat) / 20480000000), R := ((2567493247 : Rat) / 1024000000), D0 := ((2567493247 : Rat) / 1024000000), D1 := ((3531993723 : Rat) / 5120000000), D2 := ((1044048459 : Rat) / 20480000000), D3 := ((2139998054478236587 : Rat) / 10000000000000000000), D4 := ((905171719033377197 : Rat) / 3125000000000000000), LB := ((17465682659506543 : Rat) / 100000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((2567493247 : Rat) / 1024000000), R := ((51357269539 : Rat) / 20480000000), D0 := ((51357269539 : Rat) / 20480000000), D1 := ((14135379491 : Rat) / 20480000000), D2 := ((51832193 : Rat) / 1024000000), D3 := ((2136382527622767837 : Rat) / 10000000000000000000), D4 := ((7232334935128345701 : Rat) / 25000000000000000000), LB := ((186327752572657 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51357269539 : Rat) / 20480000000), R := ((25682337069 : Rat) / 10240000000), D0 := ((25682337069 : Rat) / 10240000000), D1 := ((1414278409 : Rat) / 2048000000), D2 := ((1029239261 : Rat) / 20480000000), D3 := ((2132767000767299087 : Rat) / 10000000000000000000), D4 := ((3611648058994836913 : Rat) / 12500000000000000000), LB := ((4010931891197389 : Rat) / 20000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25682337069 : Rat) / 10240000000), R := ((51372078737 : Rat) / 20480000000), D0 := ((51372078737 : Rat) / 20480000000), D1 := ((14150188689 : Rat) / 20480000000), D2 := ((510917331 : Rat) / 10240000000), D3 := ((2129151473911830337 : Rat) / 10000000000000000000), D4 := ((7214257300851001951 : Rat) / 25000000000000000000), LB := ((10866805647302691 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51372078737 : Rat) / 20480000000), R := ((6422435417 : Rat) / 2560000000), D0 := ((6422435417 : Rat) / 2560000000), D1 := ((1769699161 : Rat) / 2560000000), D2 := ((1014430063 : Rat) / 20480000000), D3 := ((2125535947056361587 : Rat) / 10000000000000000000), D4 := ((1801304620928082519 : Rat) / 6250000000000000000), LB := ((11835976186042041 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6422435417 : Rat) / 2560000000), R := ((10277377587 : Rat) / 4096000000), D0 := ((10277377587 : Rat) / 4096000000), D1 := ((14164997887 : Rat) / 20480000000), D2 := ((125878183 : Rat) / 2560000000), D3 := ((2121920420200892837 : Rat) / 10000000000000000000), D4 := ((7196179666573658201 : Rat) / 25000000000000000000), LB := ((258720511484567 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((10277377587 : Rat) / 4096000000), R := ((25697146267 : Rat) / 10240000000), D0 := ((25697146267 : Rat) / 10240000000), D1 := ((7086201243 : Rat) / 10240000000), D2 := ((199924173 : Rat) / 4096000000), D3 := ((2118304893345424087 : Rat) / 10000000000000000000), D4 := ((3593570424717493163 : Rat) / 12500000000000000000), LB := ((3542040536629043 : Rat) / 12500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25697146267 : Rat) / 10240000000), R := ((51401697133 : Rat) / 20480000000), D0 := ((51401697133 : Rat) / 20480000000), D1 := ((2835961417 : Rat) / 4096000000), D2 := ((496108133 : Rat) / 10240000000), D3 := ((2114689366489955337 : Rat) / 10000000000000000000), D4 := ((7178102032296314451 : Rat) / 25000000000000000000), LB := ((7766809520670659 : Rat) / 25000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51401697133 : Rat) / 20480000000), R := ((12852275433 : Rat) / 5120000000), D0 := ((12852275433 : Rat) / 5120000000), D1 := ((3546802921 : Rat) / 5120000000), D2 := ((984811667 : Rat) / 20480000000), D3 := ((2111073839634486587 : Rat) / 10000000000000000000), D4 := ((448066450947352661 : Rat) / 1562500000000000000), LB := ((3406730985229811 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12852275433 : Rat) / 5120000000), R := ((51416506331 : Rat) / 20480000000), D0 := ((51416506331 : Rat) / 20480000000), D1 := ((14194616283 : Rat) / 20480000000), D2 := ((244351767 : Rat) / 5120000000), D3 := ((2107458312779017837 : Rat) / 10000000000000000000), D4 := ((7160024398018970701 : Rat) / 25000000000000000000), LB := ((2333694343715359 : Rat) / 6250000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51416506331 : Rat) / 20480000000), R := ((5142391093 : Rat) / 2048000000), D0 := ((5142391093 : Rat) / 2048000000), D1 := ((7101010441 : Rat) / 10240000000), D2 := ((970002469 : Rat) / 20480000000), D3 := ((2103842785923549087 : Rat) / 10000000000000000000), D4 := ((3575492790440149413 : Rat) / 12500000000000000000), LB := ((408852610462751 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((5142391093 : Rat) / 2048000000), R := ((51431315529 : Rat) / 20480000000), D0 := ((51431315529 : Rat) / 20480000000), D1 := ((14209425481 : Rat) / 20480000000), D2 := ((96259787 : Rat) / 2048000000), D3 := ((2100227259068080337 : Rat) / 10000000000000000000), D4 := ((7141946763741626951 : Rat) / 25000000000000000000), LB := ((174642360392511 : Rat) / 390625000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51431315529 : Rat) / 20480000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((955193271 : Rat) / 20480000000), D3 := ((2096611732212611587 : Rat) / 10000000000000000000), D4 := ((1783226986650738769 : Rat) / 6250000000000000000), LB := ((2440569816951621 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((51446124727 : Rat) / 20480000000), D0 := ((51446124727 : Rat) / 20480000000), D1 := ((14224234679 : Rat) / 20480000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((7123869129464283201 : Rat) / 25000000000000000000), LB := ((5319691365687773 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((51446124727 : Rat) / 20480000000), R := ((25726764663 : Rat) / 10240000000), D0 := ((25726764663 : Rat) / 10240000000), D1 := ((7115819639 : Rat) / 10240000000), D2 := ((940384073 : Rat) / 20480000000), D3 := ((2089380678501674087 : Rat) / 10000000000000000000), D4 := ((3557415156162805663 : Rat) / 12500000000000000000), LB := ((1446696339595377 : Rat) / 2500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25726764663 : Rat) / 10240000000), R := ((2058437357 : Rat) / 819200000), D0 := ((2058437357 : Rat) / 819200000), D1 := ((14239043877 : Rat) / 20480000000), D2 := ((466489737 : Rat) / 10240000000), D3 := ((2085765151646205337 : Rat) / 10000000000000000000), D4 := ((7105791495186939451 : Rat) / 25000000000000000000), LB := ((6282713637306703 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((2058437357 : Rat) / 819200000), R := ((12867084631 : Rat) / 5120000000), D0 := ((12867084631 : Rat) / 5120000000), D1 := ((3561612119 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 163840000), D3 := ((2082149624790736587 : Rat) / 10000000000000000000), D4 := ((887094084756033447 : Rat) / 3125000000000000000), LB := ((3403887356225599 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12867084631 : Rat) / 5120000000), R := ((25741573861 : Rat) / 10240000000), D0 := ((25741573861 : Rat) / 10240000000), D1 := ((7130628837 : Rat) / 10240000000), D2 := ((229542569 : Rat) / 5120000000), D3 := ((2078534097935267837 : Rat) / 10000000000000000000), D4 := ((7087713860909595701 : Rat) / 25000000000000000000), LB := ((290304185289747 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25741573861 : Rat) / 10240000000), R := ((1287448923 : Rat) / 512000000), D0 := ((1287448923 : Rat) / 512000000), D1 := ((1784508359 : Rat) / 2560000000), D2 := ((451680539 : Rat) / 10240000000), D3 := ((2071303044224330337 : Rat) / 10000000000000000000), D4 := ((7069636226632251951 : Rat) / 25000000000000000000), LB := ((4462834904897517 : Rat) / 25000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1287448923 : Rat) / 512000000), R := ((25756383059 : Rat) / 10240000000), D0 := ((25756383059 : Rat) / 10240000000), D1 := ((1429087607 : Rat) / 2048000000), D2 := ((22213797 : Rat) / 512000000), D3 := ((2064071990513392837 : Rat) / 10000000000000000000), D4 := ((7051558592354908201 : Rat) / 25000000000000000000), LB := ((3111238984364051 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25756383059 : Rat) / 10240000000), R := ((12881893829 : Rat) / 5120000000), D0 := ((12881893829 : Rat) / 5120000000), D1 := ((3576421317 : Rat) / 5120000000), D2 := ((436871341 : Rat) / 10240000000), D3 := ((2056840936802455337 : Rat) / 10000000000000000000), D4 := ((7033480958077564451 : Rat) / 25000000000000000000), LB := ((9123257372808391 : Rat) / 20000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12881893829 : Rat) / 5120000000), R := ((25771192257 : Rat) / 10240000000), D0 := ((25771192257 : Rat) / 10240000000), D1 := ((7160247233 : Rat) / 10240000000), D2 := ((214733371 : Rat) / 5120000000), D3 := ((2049609883091517837 : Rat) / 10000000000000000000), D4 := ((7015403323800220701 : Rat) / 25000000000000000000), LB := ((1227827606768761 : Rat) / 2000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((25771192257 : Rat) / 10240000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((422062143 : Rat) / 10240000000), D3 := ((2042378829380580337 : Rat) / 10000000000000000000), D4 := ((6997325689522876951 : Rat) / 25000000000000000000), LB := ((1569348116219449 : Rat) / 2000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((5157200291 : Rat) / 2048000000), D0 := ((5157200291 : Rat) / 2048000000), D1 := ((7175056431 : Rat) / 10240000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((2035147775669642837 : Rat) / 10000000000000000000), D4 := ((6979248055245533201 : Rat) / 25000000000000000000), LB := ((242188953132369 : Rat) / 250000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((5157200291 : Rat) / 2048000000), R := ((12896703027 : Rat) / 5120000000), D0 := ((12896703027 : Rat) / 5120000000), D1 := ((718246103 : Rat) / 1024000000), D2 := ((81450589 : Rat) / 2048000000), D3 := ((2027916721958705337 : Rat) / 10000000000000000000), D4 := ((6961170420968189451 : Rat) / 25000000000000000000), LB := ((14581089034299 : Rat) / 12500000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12896703027 : Rat) / 5120000000), R := ((6452053813 : Rat) / 2560000000), D0 := ((6452053813 : Rat) / 2560000000), D1 := ((1799317557 : Rat) / 2560000000), D2 := ((199924173 : Rat) / 5120000000), D3 := ((2020685668247767837 : Rat) / 10000000000000000000), D4 := ((6943092786690845701 : Rat) / 25000000000000000000), LB := ((1611365266010467 : Rat) / 50000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6452053813 : Rat) / 2560000000), R := ((516460489 : Rat) / 204800000), D0 := ((516460489 : Rat) / 204800000), D1 := ((3606039713 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 2560000000), D3 := ((2006223560825892837 : Rat) / 10000000000000000000), D4 := ((6906937518136158201 : Rat) / 25000000000000000000), LB := ((5014765230614837 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((516460489 : Rat) / 204800000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 204800000), D3 := ((1991761453404017837 : Rat) / 10000000000000000000), D4 := ((6870782249581470701 : Rat) / 25000000000000000000), LB := ((10313202188559911 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((12926321423 : Rat) / 5120000000), D0 := ((12926321423 : Rat) / 5120000000), D1 := ((3620848911 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1977299345982142837 : Rat) / 10000000000000000000), D4 := ((6834626981026783201 : Rat) / 25000000000000000000), LB := ((16252768420997321 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((12926321423 : Rat) / 5120000000), R := ((6466863011 : Rat) / 2560000000), D0 := ((6466863011 : Rat) / 2560000000), D1 := ((362825351 : Rat) / 512000000), D2 := ((170305777 : Rat) / 5120000000), D3 := ((1962837238560267837 : Rat) / 10000000000000000000), D4 := ((6798471712472095701 : Rat) / 25000000000000000000), LB := ((22872930163388427 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6466863011 : Rat) / 2560000000), R := ((647426761 : Rat) / 256000000), D0 := ((647426761 : Rat) / 256000000), D1 := ((910765677 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 2560000000), D3 := ((1948375131138392837 : Rat) / 10000000000000000000), D4 := ((6762316443917408201 : Rat) / 25000000000000000000), LB := ((35651355407961827 : Rat) / 100000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((647426761 : Rat) / 256000000), R := ((6481672209 : Rat) / 2560000000), D0 := ((6481672209 : Rat) / 2560000000), D1 := ((1828935953 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 256000000), D3 := ((1919450916294642837 : Rat) / 10000000000000000000), D4 := ((6690005906808033201 : Rat) / 25000000000000000000), LB := ((1036565580574883 : Rat) / 500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((6481672209 : Rat) / 2560000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((66641391 : Rat) / 2560000000), D3 := ((1890526701450892837 : Rat) / 10000000000000000000), D4 := ((6617695369698658201 : Rat) / 25000000000000000000), LB := ((5188060302585007 : Rat) / 1250000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((3251943003 : Rat) / 1280000000), D0 := ((3251943003 : Rat) / 1280000000), D1 := ((7404599 : Rat) / 10240000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((6545384832589283201 : Rat) / 25000000000000000000), LB := ((1392592079479671 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((3251943003 : Rat) / 1280000000), R := ((1629673801 : Rat) / 640000000), D0 := ((1629673801 : Rat) / 640000000), D1 := ((466489737 : Rat) / 640000000), D2 := ((22213797 : Rat) / 1280000000), D3 := ((1803754056919642837 : Rat) / 10000000000000000000), D4 := ((6400763758370533201 : Rat) / 25000000000000000000), LB := ((8135782605525443 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1629673801 : Rat) / 640000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 640000000), D3 := ((1745905627232142837 : Rat) / 10000000000000000000), D4 := ((6256142684151783201 : Rat) / 25000000000000000000), LB := ((1017968355053897 : Rat) / 125000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((410899808767857142837 : Rat) / 160000000000000000000), D0 := ((410899808767857142837 : Rat) / 160000000000000000000), D1 := ((120103792767857142837 : Rat) / 160000000000000000000), D2 := ((1630208767857142837 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((5966900535714283201 : Rat) / 25000000000000000000), LB := ((6928285294328651 : Rat) / 500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((410899808767857142837 : Rat) / 160000000000000000000), R := ((823429826303571428511 : Rat) / 320000000000000000000), D0 := ((823429826303571428511 : Rat) / 320000000000000000000), D1 := ((241837794303571428511 : Rat) / 320000000000000000000), D2 := ((4890626303571428511 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 32000000000000000000), D4 := ((182789773303571348247 : Rat) / 800000000000000000000), LB := ((2579018170522951 : Rat) / 200000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((823429826303571428511 : Rat) / 320000000000000000000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((47276054267857142273 : Rat) / 320000000000000000000), D4 := ((357428502767856982309 : Rat) / 1600000000000000000000), LB := ((6145683506895261 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((165338048767857142837 : Rat) / 64000000000000000000), D0 := ((165338048767857142837 : Rat) / 64000000000000000000), D1 := ((49019642367857142837 : Rat) / 64000000000000000000), D2 := ((1630208767857142837 : Rat) / 64000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((87319364732142817031 : Rat) / 400000000000000000000), LB := ((15662136060790033 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((165338048767857142837 : Rat) / 64000000000000000000), R := ((1655010696446428571207 : Rat) / 640000000000000000000), D0 := ((1655010696446428571207 : Rat) / 640000000000000000000), D1 := ((491826632446428571207 : Rat) / 640000000000000000000), D2 := ((17932296446428571207 : Rat) / 640000000000000000000), D3 := ((44015636732142856599 : Rat) / 320000000000000000000), D4 := ((341126415089285553939 : Rat) / 1600000000000000000000), LB := ((2652679820475401 : Rat) / 500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1655010696446428571207 : Rat) / 640000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((86401064696428570361 : Rat) / 640000000000000000000), D4 := ((674101786339285393693 : Rat) / 3200000000000000000000), LB := ((2029195826779129 : Rat) / 500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((1658271113982142856881 : Rat) / 640000000000000000000), D0 := ((1658271113982142856881 : Rat) / 640000000000000000000), D1 := ((495087049982142856881 : Rat) / 640000000000000000000), D2 := ((21192713982142856881 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((166487685624999919877 : Rat) / 800000000000000000000), LB := ((1559919360027029 : Rat) / 500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1658271113982142856881 : Rat) / 640000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((83140647160714284687 : Rat) / 640000000000000000000), D4 := ((657799698660713965323 : Rat) / 3200000000000000000000), LB := ((4930765993163 : Rat) / 2000000000000000) }
]

def block266RightChunk000L : Rat := ((88263944196428571543 : Rat) / 50000000000000000000)
def block266RightChunk000R : Rat := ((829950661374999999859 : Rat) / 320000000000000000000)

def block266RightChunk000Certificate : Bool :=
  allBoxesValid block266RightChunk000 &&
  coversFromBool block266RightChunk000 block266RightChunk000L block266RightChunk000R

theorem block266RightChunk000Certificate_eq_true :
    block266RightChunk000Certificate = true := by
  native_decide

def block266RightChunk001 : List RatBox := [
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((332306306303571428511 : Rat) / 128000000000000000000), D0 := ((332306306303571428511 : Rat) / 128000000000000000000), D1 := ((99669493503571428511 : Rat) / 128000000000000000000), D2 := ((4890626303571428511 : Rat) / 128000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((324824327410714125569 : Rat) / 1600000000000000000000), LB := ((2076822231196873 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((332306306303571428511 : Rat) / 128000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((79880229624999999013 : Rat) / 640000000000000000000), D4 := ((641497610982142536953 : Rat) / 3200000000000000000000), LB := ((9702855046124781 : Rat) / 5000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((1664791949053571428229 : Rat) / 640000000000000000000), D0 := ((1664791949053571428229 : Rat) / 640000000000000000000), D1 := ((501607885053571428229 : Rat) / 640000000000000000000), D2 := ((27713549053571428229 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((39584160446428551423 : Rat) / 200000000000000000000), LB := ((102331256826943 : Rat) / 50000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1664791949053571428229 : Rat) / 640000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((76619812089285713339 : Rat) / 640000000000000000000), D4 := ((625195523303571108583 : Rat) / 3200000000000000000000), LB := ((23878309593390323 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((308522239732142697199 : Rat) / 1600000000000000000000), LB := ((29593615548118013 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((608893435624999680213 : Rat) / 3200000000000000000000), LB := ((37583371565628187 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((150185597946428491507 : Rat) / 800000000000000000000), LB := ((239177438883037 : Rat) / 50000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((592591347946428251843 : Rat) / 3200000000000000000000), LB := ((6035257569807051 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((292220152053571268829 : Rat) / 1600000000000000000000), LB := ((21012799905344437 : Rat) / 10000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((71017277053571388661 : Rat) / 400000000000000000000), LB := ((234865413715033 : Rat) / 40000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((275918064374999840459 : Rat) / 1600000000000000000000), LB := ((529473141138509 : Rat) / 50000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((133883510267857063137 : Rat) / 800000000000000000000), LB := ((6214993591213247 : Rat) / 1000000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((15716558303571418619 : Rat) / 100000000000000000000), LB := ((1018563071975731 : Rat) / 500000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((54715189374999960291 : Rat) / 400000000000000000000), LB := ((4986961723657979 : Rat) / 100000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((23282072767857123053 : Rat) / 200000000000000000000), LB := ((9928142922962513 : Rat) / 100000000000000000) },
  { w1 := ((2572133444579613 : Rat) / 2500000000000000), w2 := ((1712554528473291 : Rat) / 62500000000000000), w3 := ((29565097464078177 : Rat) / 100000000000000000), w4 := (0 : Rat), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((69915275535714283201 : Rat) / 25000000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((69136859375000000057 : Rat) / 25000000000000000000), D0 := ((69136859375000000057 : Rat) / 25000000000000000000), D1 := ((23699981875000000057 : Rat) / 25000000000000000000), D2 := ((5188484375000000057 : Rat) / 25000000000000000000), D3 := ((2225924910714285929 : Rat) / 50000000000000000000), D4 := ((3782757232142852217 : Rat) / 50000000000000000000), LB := ((8378699218596353 : Rat) / 10000000000000000000) }
]

def block266RightChunk001L : Rat := ((829950661374999999859 : Rat) / 320000000000000000000)
def block266RightChunk001R : Rat := ((69136859375000000057 : Rat) / 25000000000000000000)

def block266RightChunk001Certificate : Bool :=
  allBoxesValid block266RightChunk001 &&
  coversFromBool block266RightChunk001 block266RightChunk001L block266RightChunk001R

theorem block266RightChunk001Certificate_eq_true :
    block266RightChunk001Certificate = true := by
  native_decide

def block266RightChainCertificate : Bool :=
  decide (
    block266RightL = ((88263944196428571543 : Rat) / 50000000000000000000) /\
    ((829950661374999999859 : Rat) / 320000000000000000000) = ((829950661374999999859 : Rat) / 320000000000000000000) /\
    ((69136859375000000057 : Rat) / 25000000000000000000) = block266RightR)

theorem block266RightChainCertificate_eq_true :
    block266RightChainCertificate = true := by
  native_decide

def block266LeftBoxCount : Nat := boxCount block266LeftBoxes
def block266RightBoxCount : Nat := 116

def block266_rational_certificate : Prop :=
    block266LeftCertificate = true /\
    block266RightChainCertificate = true /\
    block266RightChunk000Certificate = true /\
    block266RightChunk001Certificate = true

theorem block266_rational_certificate_proof :
    block266_rational_certificate := by
  exact ⟨block266LeftCertificate_eq_true, block266RightChainCertificate_eq_true, block266RightChunk000Certificate_eq_true, block266RightChunk001Certificate_eq_true⟩

end Block266
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block266

open Set

def block266W1 : Rat := ((2572133444579613 : Rat) / 2500000000000000)
def block266W2 : Rat := ((1712554528473291 : Rat) / 62500000000000000)
def block266W3 : Rat := ((29565097464078177 : Rat) / 100000000000000000)
def block266W4 : Rat := (0 : Rat)
def block266S1 : Rat := ((18174751 : Rat) / 10000000)
def block266S2 : Rat := ((511587 : Rat) / 200000)
def block266S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block266S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block266V (y : ℝ) : ℝ :=
  ratPotential block266W1 block266W2 block266W3 block266W4 block266S1 block266S2 block266S3 block266S4 y

def block266LeftParamsCertificate : Bool :=
  allBoxesSameParams block266LeftBoxes block266W1 block266W2 block266W3 block266W4 block266S1 block266S2 block266S3 block266S4

theorem block266LeftParamsCertificate_eq_true :
    block266LeftParamsCertificate = true := by
  native_decide

theorem block266_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block266LeftL : ℝ) (block266LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block266S1 : ℝ))
    (hy2ne : y ≠ (block266S2 : ℝ))
    (hy3ne : y ≠ (block266S3 : ℝ))
    (hy4ne : y ≠ (block266S4 : ℝ)) :
    0 < block266V y := by
  have hcert := block266LeftCertificate_eq_true
  unfold block266LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block266LeftBoxes) (lo := block266LeftL) (hi := block266LeftR)
    (w1 := block266W1) (w2 := block266W2) (w3 := block266W3) (w4 := block266W4)
    (s1 := block266S1) (s2 := block266S2) (s3 := block266S3) (s4 := block266S4)
    hboxes hcover block266LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block266RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block266RightChunk000 block266W1 block266W2 block266W3 block266W4 block266S1 block266S2 block266S3 block266S4

theorem block266RightChunk000ParamsCertificate_eq_true :
    block266RightChunk000ParamsCertificate = true := by
  native_decide

theorem block266_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block266RightChunk000L : ℝ) (block266RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block266S1 : ℝ))
    (hy2ne : y ≠ (block266S2 : ℝ))
    (hy3ne : y ≠ (block266S3 : ℝ))
    (hy4ne : y ≠ (block266S4 : ℝ)) :
    0 < block266V y := by
  have hcert := block266RightChunk000Certificate_eq_true
  unfold block266RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block266RightChunk000) (lo := block266RightChunk000L) (hi := block266RightChunk000R)
    (w1 := block266W1) (w2 := block266W2) (w3 := block266W3) (w4 := block266W4)
    (s1 := block266S1) (s2 := block266S2) (s3 := block266S3) (s4 := block266S4)
    hboxes hcover block266RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block266RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block266RightChunk001 block266W1 block266W2 block266W3 block266W4 block266S1 block266S2 block266S3 block266S4

theorem block266RightChunk001ParamsCertificate_eq_true :
    block266RightChunk001ParamsCertificate = true := by
  native_decide

theorem block266_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block266RightChunk001L : ℝ) (block266RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block266S1 : ℝ))
    (hy2ne : y ≠ (block266S2 : ℝ))
    (hy3ne : y ≠ (block266S3 : ℝ))
    (hy4ne : y ≠ (block266S4 : ℝ)) :
    0 < block266V y := by
  have hcert := block266RightChunk001Certificate_eq_true
  unfold block266RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block266RightChunk001) (lo := block266RightChunk001L) (hi := block266RightChunk001R)
    (w1 := block266W1) (w2 := block266W2) (w3 := block266W3) (w4 := block266W4)
    (s1 := block266S1) (s2 := block266S2) (s3 := block266S3) (s4 := block266S4)
    hboxes hcover block266RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block266_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block266RightL : ℝ) (block266RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block266S1 : ℝ))
    (hy2ne : y ≠ (block266S2 : ℝ))
    (hy3ne : y ≠ (block266S3 : ℝ))
    (hy4ne : y ≠ (block266S4 : ℝ)) :
    0 < block266V y := by
  by_cases h0 : y ≤ (block266RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block266RightChunk000L : ℝ) (block266RightChunk000R : ℝ) := by
      have hL : (block266RightChunk000L : ℝ) = (block266RightL : ℝ) := by
        norm_num [block266RightChunk000L, block266RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block266_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block266RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block266RightChunk001L : ℝ) = (block266RightChunk000R : ℝ) := by
      norm_num [block266RightChunk001L, block266RightChunk000R]
    have hR : (block266RightChunk001R : ℝ) = (block266RightR : ℝ) := by
      norm_num [block266RightChunk001R, block266RightR]
    have hyc : y ∈ Icc (block266RightChunk001L : ℝ) (block266RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block266_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block266_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block266LeftL : ℝ) (block266LeftR : ℝ) →
    y ≠ 0 → y ≠ (block266S1 : ℝ) → y ≠ (block266S2 : ℝ) →
    y ≠ (block266S3 : ℝ) → y ≠ (block266S4 : ℝ) → 0 < block266V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block266RightL : ℝ) (block266RightR : ℝ) →
    y ≠ 0 → y ≠ (block266S1 : ℝ) → y ≠ (block266S2 : ℝ) →
    y ≠ (block266S3 : ℝ) → y ≠ (block266S4 : ℝ) → 0 < block266V y)

theorem block266_reallog_certificate_proof :
    block266_reallog_certificate := by
  exact ⟨block266_left_V_pos, block266_right_V_pos⟩

end Block266
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block266.block266V
#check Erdos1038Lean.M1817475.Block266.block266_left_V_pos
#check Erdos1038Lean.M1817475.Block266.block266_right_V_pos
#check Erdos1038Lean.M1817475.Block266.block266_reallog_certificate_proof
