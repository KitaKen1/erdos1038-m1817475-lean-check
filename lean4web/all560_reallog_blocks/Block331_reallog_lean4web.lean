/-
Self-contained Lean4Web paste file.
Block 331 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block331

def block331LeftL : Rat := ((9407149553571428607 : Rat) / 12500000000000000000)
def block331LeftR : Rat := ((37638372767857142999 : Rat) / 50000000000000000000)
def block331RightL : Rat := ((21907149553571428607 : Rat) / 12500000000000000000)
def block331RightR : Rat := ((137638372767857142999 : Rat) / 50000000000000000000)

def block331LeftBoxes : List RatBox := [
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((9407149553571428607 : Rat) / 12500000000000000000), R := ((37638372767857142999 : Rat) / 50000000000000000000), D0 := ((37638372767857142999 : Rat) / 50000000000000000000), D1 := ((13311289196428571393 : Rat) / 12500000000000000000), D2 := ((22567037946428571393 : Rat) / 12500000000000000000), D3 := ((96034204553571428433 : Rat) / 50000000000000000000), D4 := ((10098990821428570917 : Rat) / 5000000000000000000), LB := ((3268615800432681 : Rat) / 500000000000000000) }
]

def block331LeftCertificate : Bool :=
  allBoxesValid block331LeftBoxes &&
  coversFromBool block331LeftBoxes block331LeftL block331LeftR

theorem block331LeftCertificate_eq_true :
    block331LeftCertificate = true := by
  native_decide

def block331RightChunk000 : List RatBox := [
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21907149553571428607 : Rat) / 12500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((811289196428571393 : Rat) / 12500000000000000000), D2 := ((10067037946428571393 : Rat) / 12500000000000000000), D3 := ((46034204553571428433 : Rat) / 50000000000000000000), D4 := ((5098990821428570917 : Rat) / 5000000000000000000), LB := ((125880802861211 : Rat) / 62500000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42789047767857142861 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((10089198427564157 : Rat) / 50000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24277550267857142861 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((3252464229006663 : Rat) / 25000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19649675892857142861 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((872085083295171 : Rat) / 10000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17335738705357142861 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((5031274505244171 : Rat) / 200000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((15021801517857142861 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((1143283281285519 : Rat) / 50000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13864832924107142861 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((20568951912792177 : Rat) / 10000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12707864330357142861 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((15405146762911437 : Rat) / 2000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((12129380033482142861 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((5914450501369461 : Rat) / 10000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11550895736607142861 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((1143922479036541 : Rat) / 200000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11261653588169642861 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((199073375691727 : Rat) / 62500000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10972411439732142861 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((250950170026229 : Rat) / 250000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10683169291294642861 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((4610401345436943 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10538548217075892861 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((2395773048308493 : Rat) / 625000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10393927142857142861 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((31586511014760343 : Rat) / 10000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10249306068638392861 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((12951047047262687 : Rat) / 5000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((10104684994419642861 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((10658945190460123 : Rat) / 5000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9960063920200892861 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((715047153270143 : Rat) / 400000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9815442845982142861 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((7811599557011051 : Rat) / 5000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9670821771763392861 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((14609685918304527 : Rat) / 10000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9526200697544642861 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((372287535311773 : Rat) / 250000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9381579623325892861 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((4132597171616903 : Rat) / 2500000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9236958549107142861 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((9797437773624157 : Rat) / 5000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((9092337474888392861 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((4832273348934657 : Rat) / 2000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8947716400669642861 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((15157737265735771 : Rat) / 5000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8803095326450892861 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((19076826841338407 : Rat) / 5000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((6407626219 : Rat) / 2560000000), D0 := ((6407626219 : Rat) / 2560000000), D1 := ((1754889963 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8658474252232142861 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((1194630741405571 : Rat) / 250000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6407626219 : Rat) / 2560000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((140687381 : Rat) / 2560000000), D3 := ((8513853178013392861 : Rat) / 50000000000000000000), D4 := ((6734778419363836799 : Rat) / 25000000000000000000), LB := ((2966747019703647 : Rat) / 500000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8369232103794642861 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((4369712832577699 : Rat) / 2000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((8079989955357142861 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((5630246082007573 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7790747806919642861 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((10140149677178911 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7501505658482142861 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((750105149723377 : Rat) / 125000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6923021361607142861 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((796779237529699 : Rat) / 200000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028940052767857142861 : Rat) / 400000000000000000000), D0 := ((1028940052767857142861 : Rat) / 400000000000000000000), D1 := ((301950012767857142861 : Rat) / 400000000000000000000), D2 := ((5766052767857142861 : Rat) / 400000000000000000000), D3 := ((5766052767857142861 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((4270278703316299 : Rat) / 100000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028940052767857142861 : Rat) / 400000000000000000000), R := ((517353052767857142861 : Rat) / 200000000000000000000), D0 := ((517353052767857142861 : Rat) / 200000000000000000000), D1 := ((153858032767857142861 : Rat) / 200000000000000000000), D2 := ((5766052767857142861 : Rat) / 200000000000000000000), D3 := ((40362369375000000027 : Rat) / 400000000000000000000), D4 := ((80007998660714245923 : Rat) / 400000000000000000000), LB := ((15186166816601843 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517353052767857142861 : Rat) / 200000000000000000000), R := ((1040472158303571428583 : Rat) / 400000000000000000000), D0 := ((1040472158303571428583 : Rat) / 400000000000000000000), D1 := ((313482118303571428583 : Rat) / 400000000000000000000), D2 := ((17298158303571428583 : Rat) / 400000000000000000000), D3 := ((17298158303571428583 : Rat) / 200000000000000000000), D4 := ((37120972946428551531 : Rat) / 200000000000000000000), LB := ((659741018121069 : Rat) / 125000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1040472158303571428583 : Rat) / 400000000000000000000), R := ((261559552767857142861 : Rat) / 100000000000000000000), D0 := ((261559552767857142861 : Rat) / 100000000000000000000), D1 := ((79812042767857142861 : Rat) / 100000000000000000000), D2 := ((5766052767857142861 : Rat) / 100000000000000000000), D3 := ((5766052767857142861 : Rat) / 80000000000000000000), D4 := ((68475893124999960201 : Rat) / 400000000000000000000), LB := ((1537625532524553 : Rat) / 250000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261559552767857142861 : Rat) / 100000000000000000000), R := ((210400852767857142861 : Rat) / 80000000000000000000), D0 := ((210400852767857142861 : Rat) / 80000000000000000000), D1 := ((65002844767857142861 : Rat) / 80000000000000000000), D2 := ((5766052767857142861 : Rat) / 80000000000000000000), D3 := ((5766052767857142861 : Rat) / 100000000000000000000), D4 := ((3135492017857140867 : Rat) / 20000000000000000000), LB := ((8621070451108853 : Rat) / 500000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((210400852767857142861 : Rat) / 80000000000000000000), R := ((528885158303571428583 : Rat) / 200000000000000000000), D0 := ((528885158303571428583 : Rat) / 200000000000000000000), D1 := ((165390138303571428583 : Rat) / 200000000000000000000), D2 := ((17298158303571428583 : Rat) / 200000000000000000000), D3 := ((17298158303571428583 : Rat) / 400000000000000000000), D4 := ((56943787589285674479 : Rat) / 400000000000000000000), LB := ((205077567935201 : Rat) / 5000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528885158303571428583 : Rat) / 200000000000000000000), R := ((133662802767857142861 : Rat) / 50000000000000000000), D0 := ((133662802767857142861 : Rat) / 50000000000000000000), D1 := ((42789047767857142861 : Rat) / 50000000000000000000), D2 := ((5766052767857142861 : Rat) / 50000000000000000000), D3 := ((5766052767857142861 : Rat) / 200000000000000000000), D4 := ((25588867410714265809 : Rat) / 200000000000000000000), LB := ((2847348368567837 : Rat) / 50000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133662802767857142861 : Rat) / 50000000000000000000), R := ((269313390535714285791 : Rat) / 100000000000000000000), D0 := ((269313390535714285791 : Rat) / 100000000000000000000), D1 := ((87565880535714285791 : Rat) / 100000000000000000000), D2 := ((13519890535714285791 : Rat) / 100000000000000000000), D3 := ((1987785000000000069 : Rat) / 100000000000000000000), D4 := ((4955703660714280737 : Rat) / 50000000000000000000), LB := ((10862078347380577 : Rat) / 100000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((269313390535714285791 : Rat) / 100000000000000000000), R := ((13565058776785714293 : Rat) / 5000000000000000000), D0 := ((13565058776785714293 : Rat) / 5000000000000000000), D1 := ((4477683276785714293 : Rat) / 5000000000000000000), D2 := ((775383776785714293 : Rat) / 5000000000000000000), D3 := ((1987785000000000069 : Rat) / 50000000000000000000), D4 := ((1584724464285712281 : Rat) / 20000000000000000000), LB := ((4681135231039801 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((13565058776785714293 : Rat) / 5000000000000000000), R := ((1087192487142857143509 : Rat) / 400000000000000000000), D0 := ((1087192487142857143509 : Rat) / 400000000000000000000), D1 := ((360202447142857143509 : Rat) / 400000000000000000000), D2 := ((64018487142857143509 : Rat) / 400000000000000000000), D3 := ((17890065000000000621 : Rat) / 400000000000000000000), D4 := ((741979665178570167 : Rat) / 12500000000000000000), LB := ((1877579181455369 : Rat) / 100000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1087192487142857143509 : Rat) / 400000000000000000000), R := ((544590136071428571789 : Rat) / 200000000000000000000), D0 := ((544590136071428571789 : Rat) / 200000000000000000000), D1 := ((181095116071428571789 : Rat) / 200000000000000000000), D2 := ((33003136071428571789 : Rat) / 200000000000000000000), D3 := ((1987785000000000069 : Rat) / 40000000000000000000), D4 := ((870222571428569811 : Rat) / 16000000000000000000), LB := ((1428507988229899 : Rat) / 200000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((544590136071428571789 : Rat) / 200000000000000000000), R := ((87213933171428571489 : Rat) / 32000000000000000000), D0 := ((87213933171428571489 : Rat) / 32000000000000000000), D1 := ((29054729971428571489 : Rat) / 32000000000000000000), D2 := ((5360013171428571489 : Rat) / 32000000000000000000), D3 := ((41743485000000001449 : Rat) / 800000000000000000000), D4 := ((9883889642857122603 : Rat) / 200000000000000000000), LB := ((904916671033501 : Rat) / 100000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87213933171428571489 : Rat) / 32000000000000000000), R := ((1091168057142857143647 : Rat) / 400000000000000000000), D0 := ((1091168057142857143647 : Rat) / 400000000000000000000), D1 := ((364178017142857143647 : Rat) / 400000000000000000000), D2 := ((67994057142857143647 : Rat) / 400000000000000000000), D3 := ((21865635000000000759 : Rat) / 400000000000000000000), D4 := ((37547773571428490343 : Rat) / 800000000000000000000), LB := ((5241362933697091 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1091168057142857143647 : Rat) / 400000000000000000000), R := ((2184323899285714287363 : Rat) / 800000000000000000000), D0 := ((2184323899285714287363 : Rat) / 800000000000000000000), D1 := ((730343819285714287363 : Rat) / 800000000000000000000), D2 := ((137975899285714287363 : Rat) / 800000000000000000000), D3 := ((45719055000000001587 : Rat) / 800000000000000000000), D4 := ((17779994285714245137 : Rat) / 400000000000000000000), LB := ((2132873278383851 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2184323899285714287363 : Rat) / 800000000000000000000), R := ((874127116714285714959 : Rat) / 320000000000000000000), D0 := ((874127116714285714959 : Rat) / 320000000000000000000), D1 := ((292535084714285714959 : Rat) / 320000000000000000000), D2 := ((55587916714285714959 : Rat) / 320000000000000000000), D3 := ((93425895000000003243 : Rat) / 1600000000000000000000), D4 := ((6714440714285698041 : Rat) / 160000000000000000000), LB := ((12106645050909831 : Rat) / 2500000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((874127116714285714959 : Rat) / 320000000000000000000), R := ((273288960535714285929 : Rat) / 100000000000000000000), D0 := ((273288960535714285929 : Rat) / 100000000000000000000), D1 := ((91541450535714285929 : Rat) / 100000000000000000000), D2 := ((17495460535714285929 : Rat) / 100000000000000000000), D3 := ((5963355000000000207 : Rat) / 100000000000000000000), D4 := ((65156622142856980341 : Rat) / 1600000000000000000000), LB := ((482353930281329 : Rat) / 125000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((273288960535714285929 : Rat) / 100000000000000000000), R := ((4374611153571428574933 : Rat) / 1600000000000000000000), D0 := ((4374611153571428574933 : Rat) / 1600000000000000000000), D1 := ((1466650993571428574933 : Rat) / 1600000000000000000000), D2 := ((281915153571428574933 : Rat) / 1600000000000000000000), D3 := ((97401465000000003381 : Rat) / 1600000000000000000000), D4 := ((3948052321428561267 : Rat) / 100000000000000000000), LB := ((191825279456187 : Rat) / 62500000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4374611153571428574933 : Rat) / 1600000000000000000000), R := ((2188299469285714287501 : Rat) / 800000000000000000000), D0 := ((2188299469285714287501 : Rat) / 800000000000000000000), D1 := ((734319389285714287501 : Rat) / 800000000000000000000), D2 := ((141951469285714287501 : Rat) / 800000000000000000000), D3 := ((1987785000000000069 : Rat) / 32000000000000000000), D4 := ((61181052142856980203 : Rat) / 1600000000000000000000), LB := ((12396892116361413 : Rat) / 5000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2188299469285714287501 : Rat) / 800000000000000000000), R := ((4378586723571428575071 : Rat) / 1600000000000000000000), D0 := ((4378586723571428575071 : Rat) / 1600000000000000000000), D1 := ((1470626563571428575071 : Rat) / 1600000000000000000000), D2 := ((285890723571428575071 : Rat) / 1600000000000000000000), D3 := ((101377035000000003519 : Rat) / 1600000000000000000000), D4 := ((29596633571428490067 : Rat) / 800000000000000000000), LB := ((5239783760519201 : Rat) / 2500000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4378586723571428575071 : Rat) / 1600000000000000000000), R := ((219028725428571428757 : Rat) / 80000000000000000000), D0 := ((219028725428571428757 : Rat) / 80000000000000000000), D1 := ((73630717428571428757 : Rat) / 80000000000000000000), D2 := ((14393925428571428757 : Rat) / 80000000000000000000), D3 := ((25841205000000000897 : Rat) / 400000000000000000000), D4 := ((11441096428571396013 : Rat) / 320000000000000000000), LB := ((9632138415995861 : Rat) / 5000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((219028725428571428757 : Rat) / 80000000000000000000), R := ((4382562293571428575209 : Rat) / 1600000000000000000000), D0 := ((4382562293571428575209 : Rat) / 1600000000000000000000), D1 := ((1474602133571428575209 : Rat) / 1600000000000000000000), D2 := ((289866293571428575209 : Rat) / 1600000000000000000000), D3 := ((105352605000000003657 : Rat) / 1600000000000000000000), D4 := ((13804424285714244999 : Rat) / 400000000000000000000), LB := ((1979716224468131 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4382562293571428575209 : Rat) / 1600000000000000000000), R := ((2192275039285714287639 : Rat) / 800000000000000000000), D0 := ((2192275039285714287639 : Rat) / 800000000000000000000), D1 := ((738294959285714287639 : Rat) / 800000000000000000000), D2 := ((145927039285714287639 : Rat) / 800000000000000000000), D3 := ((53670195000000001863 : Rat) / 800000000000000000000), D4 := ((53229912142856979927 : Rat) / 1600000000000000000000), LB := ((44255782379063 : Rat) / 19531250000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2192275039285714287639 : Rat) / 800000000000000000000), R := ((4386537863571428575347 : Rat) / 1600000000000000000000), D0 := ((4386537863571428575347 : Rat) / 1600000000000000000000), D1 := ((1478577703571428575347 : Rat) / 1600000000000000000000), D2 := ((293841863571428575347 : Rat) / 1600000000000000000000), D3 := ((21865635000000000759 : Rat) / 320000000000000000000), D4 := ((25621063571428489929 : Rat) / 800000000000000000000), LB := ((27965803295795233 : Rat) / 10000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4386537863571428575347 : Rat) / 1600000000000000000000), R := ((548565706071428571927 : Rat) / 200000000000000000000), D0 := ((548565706071428571927 : Rat) / 200000000000000000000), D1 := ((185070686071428571927 : Rat) / 200000000000000000000), D2 := ((36978706071428571927 : Rat) / 200000000000000000000), D3 := ((13914495000000000483 : Rat) / 200000000000000000000), D4 := ((49254342142856979789 : Rat) / 1600000000000000000000), LB := ((8962725000868227 : Rat) / 2500000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((548565706071428571927 : Rat) / 200000000000000000000), R := ((2196250609285714287777 : Rat) / 800000000000000000000), D0 := ((2196250609285714287777 : Rat) / 800000000000000000000), D1 := ((742270529285714287777 : Rat) / 800000000000000000000), D2 := ((149902609285714287777 : Rat) / 800000000000000000000), D3 := ((57645765000000002001 : Rat) / 800000000000000000000), D4 := ((1181663928571424493 : Rat) / 40000000000000000000), LB := ((11369348660628109 : Rat) / 100000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2196250609285714287777 : Rat) / 800000000000000000000), R := ((1099119197142857143923 : Rat) / 400000000000000000000), D0 := ((1099119197142857143923 : Rat) / 400000000000000000000), D1 := ((372129157142857143923 : Rat) / 400000000000000000000), D2 := ((75945197142857143923 : Rat) / 400000000000000000000), D3 := ((5963355000000000207 : Rat) / 80000000000000000000), D4 := ((21645493571428489791 : Rat) / 800000000000000000000), LB := ((3221052825638171 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1099119197142857143923 : Rat) / 400000000000000000000), R := ((440045235857142857583 : Rat) / 160000000000000000000), D0 := ((440045235857142857583 : Rat) / 160000000000000000000), D1 := ((149249219857142857583 : Rat) / 160000000000000000000), D2 := ((30775635857142857583 : Rat) / 160000000000000000000), D3 := ((61621335000000002139 : Rat) / 800000000000000000000), D4 := ((9828854285714244861 : Rat) / 400000000000000000000), LB := ((7663768595017273 : Rat) / 1000000000000000000) },
  { w1 := ((9478190371674101 : Rat) / 10000000000000000), w2 := ((4717759522426041 : Rat) / 100000000000000000), w3 := ((717743943415349 : Rat) / 5000000000000000), w4 := ((6849016726919209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133662802767857142861 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((440045235857142857583 : Rat) / 160000000000000000000), R := ((137638372767857142999 : Rat) / 50000000000000000000), D0 := ((137638372767857142999 : Rat) / 50000000000000000000), D1 := ((46764617767857142999 : Rat) / 50000000000000000000), D2 := ((9741622767857142999 : Rat) / 50000000000000000000), D3 := ((1987785000000000069 : Rat) / 25000000000000000000), D4 := ((17669923571428489653 : Rat) / 800000000000000000000), LB := ((13679205915291481 : Rat) / 1000000000000000000) }
]

def block331RightChunk000L : Rat := ((21907149553571428607 : Rat) / 12500000000000000000)
def block331RightChunk000R : Rat := ((137638372767857142999 : Rat) / 50000000000000000000)

def block331RightChunk000Certificate : Bool :=
  allBoxesValid block331RightChunk000 &&
  coversFromBool block331RightChunk000 block331RightChunk000L block331RightChunk000R

theorem block331RightChunk000Certificate_eq_true :
    block331RightChunk000Certificate = true := by
  native_decide

def block331RightChainCertificate : Bool :=
  decide (
    block331RightL = ((21907149553571428607 : Rat) / 12500000000000000000) /\
    ((137638372767857142999 : Rat) / 50000000000000000000) = block331RightR)

theorem block331RightChainCertificate_eq_true :
    block331RightChainCertificate = true := by
  native_decide

def block331LeftBoxCount : Nat := boxCount block331LeftBoxes
def block331RightBoxCount : Nat := 61

def block331_rational_certificate : Prop :=
    block331LeftCertificate = true /\
    block331RightChainCertificate = true /\
    block331RightChunk000Certificate = true

theorem block331_rational_certificate_proof :
    block331_rational_certificate := by
  exact ⟨block331LeftCertificate_eq_true, block331RightChainCertificate_eq_true, block331RightChunk000Certificate_eq_true⟩

end Block331
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block331

open Set

def block331W1 : Rat := ((9478190371674101 : Rat) / 10000000000000000)
def block331W2 : Rat := ((4717759522426041 : Rat) / 100000000000000000)
def block331W3 : Rat := ((717743943415349 : Rat) / 5000000000000000)
def block331W4 : Rat := ((6849016726919209 : Rat) / 50000000000000000)
def block331S1 : Rat := ((18174751 : Rat) / 10000000)
def block331S2 : Rat := ((511587 : Rat) / 200000)
def block331S3 : Rat := ((133662802767857142861 : Rat) / 50000000000000000000)
def block331S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block331V (y : ℝ) : ℝ :=
  ratPotential block331W1 block331W2 block331W3 block331W4 block331S1 block331S2 block331S3 block331S4 y

def block331LeftParamsCertificate : Bool :=
  allBoxesSameParams block331LeftBoxes block331W1 block331W2 block331W3 block331W4 block331S1 block331S2 block331S3 block331S4

theorem block331LeftParamsCertificate_eq_true :
    block331LeftParamsCertificate = true := by
  native_decide

theorem block331_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block331LeftL : ℝ) (block331LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block331S1 : ℝ))
    (hy2ne : y ≠ (block331S2 : ℝ))
    (hy3ne : y ≠ (block331S3 : ℝ))
    (hy4ne : y ≠ (block331S4 : ℝ)) :
    0 < block331V y := by
  have hcert := block331LeftCertificate_eq_true
  unfold block331LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block331LeftBoxes) (lo := block331LeftL) (hi := block331LeftR)
    (w1 := block331W1) (w2 := block331W2) (w3 := block331W3) (w4 := block331W4)
    (s1 := block331S1) (s2 := block331S2) (s3 := block331S3) (s4 := block331S4)
    hboxes hcover block331LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block331RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block331RightChunk000 block331W1 block331W2 block331W3 block331W4 block331S1 block331S2 block331S3 block331S4

theorem block331RightChunk000ParamsCertificate_eq_true :
    block331RightChunk000ParamsCertificate = true := by
  native_decide

theorem block331_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block331RightChunk000L : ℝ) (block331RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block331S1 : ℝ))
    (hy2ne : y ≠ (block331S2 : ℝ))
    (hy3ne : y ≠ (block331S3 : ℝ))
    (hy4ne : y ≠ (block331S4 : ℝ)) :
    0 < block331V y := by
  have hcert := block331RightChunk000Certificate_eq_true
  unfold block331RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block331RightChunk000) (lo := block331RightChunk000L) (hi := block331RightChunk000R)
    (w1 := block331W1) (w2 := block331W2) (w3 := block331W3) (w4 := block331W4)
    (s1 := block331S1) (s2 := block331S2) (s3 := block331S3) (s4 := block331S4)
    hboxes hcover block331RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block331_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block331RightL : ℝ) (block331RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block331S1 : ℝ))
    (hy2ne : y ≠ (block331S2 : ℝ))
    (hy3ne : y ≠ (block331S3 : ℝ))
    (hy4ne : y ≠ (block331S4 : ℝ)) :
    0 < block331V y := by
  have hL : (block331RightChunk000L : ℝ) = (block331RightL : ℝ) := by
    norm_num [block331RightChunk000L, block331RightL]
  have hR : (block331RightChunk000R : ℝ) = (block331RightR : ℝ) := by
    norm_num [block331RightChunk000R, block331RightR]
  have hyc : y ∈ Icc (block331RightChunk000L : ℝ) (block331RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block331_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block331_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block331LeftL : ℝ) (block331LeftR : ℝ) →
    y ≠ 0 → y ≠ (block331S1 : ℝ) → y ≠ (block331S2 : ℝ) →
    y ≠ (block331S3 : ℝ) → y ≠ (block331S4 : ℝ) → 0 < block331V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block331RightL : ℝ) (block331RightR : ℝ) →
    y ≠ 0 → y ≠ (block331S1 : ℝ) → y ≠ (block331S2 : ℝ) →
    y ≠ (block331S3 : ℝ) → y ≠ (block331S4 : ℝ) → 0 < block331V y)

theorem block331_reallog_certificate_proof :
    block331_reallog_certificate := by
  exact ⟨block331_left_V_pos, block331_right_V_pos⟩

end Block331
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block331.block331V
#check Erdos1038Lean.M1817475.Block331.block331_left_V_pos
#check Erdos1038Lean.M1817475.Block331.block331_right_V_pos
#check Erdos1038Lean.M1817475.Block331.block331_reallog_certificate_proof
