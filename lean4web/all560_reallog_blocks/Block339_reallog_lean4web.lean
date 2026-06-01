/-
Self-contained Lean4Web paste file.
Block 339 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block339

def block339LeftL : Rat := ((1877520089285714293 : Rat) / 2500000000000000000)
def block339LeftR : Rat := ((37560176339285714431 : Rat) / 50000000000000000000)
def block339RightL : Rat := ((4377520089285714293 : Rat) / 2500000000000000000)
def block339RightR : Rat := ((137560176339285714431 : Rat) / 50000000000000000000)

def block339LeftBoxes : List RatBox := [
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1877520089285714293 : Rat) / 2500000000000000000), R := ((37560176339285714431 : Rat) / 50000000000000000000), D0 := ((37560176339285714431 : Rat) / 50000000000000000000), D1 := ((2666167660714285707 : Rat) / 2500000000000000000), D2 := ((4517317410714285707 : Rat) / 2500000000000000000), D3 := ((19191201624999999973 : Rat) / 10000000000000000000), D4 := ((50534052321428568869 : Rat) / 25000000000000000000), LB := ((6383666328558579 : Rat) / 1000000000000000000) }
]

def block339LeftCertificate : Bool :=
  allBoxesValid block339LeftBoxes &&
  coversFromBool block339LeftBoxes block339LeftL block339LeftR

theorem block339LeftCertificate_eq_true :
    block339LeftCertificate = true := by
  native_decide

def block339RightChunk000 : List RatBox := [
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4377520089285714293 : Rat) / 2500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((166167660714285707 : Rat) / 2500000000000000000), D2 := ((2017317410714285707 : Rat) / 2500000000000000000), D3 := ((9191201624999999973 : Rat) / 10000000000000000000), D4 := ((25534052321428568869 : Rat) / 25000000000000000000), LB := ((1942428632071227 : Rat) / 1000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((1705306196428571429 : Rat) / 2000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((9235620791983641 : Rat) / 50000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((964846296428571429 : Rat) / 2000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((2979995472955031 : Rat) / 25000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((779731321428571429 : Rat) / 2000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((7890404106897739 : Rat) / 100000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((687173833928571429 : Rat) / 2000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((1896933859683947 : Rat) / 100000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((594616346428571429 : Rat) / 2000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((141102046750321 : Rat) / 7812500000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((548337602678571429 : Rat) / 2000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((5296045009063749 : Rat) / 250000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((525198230803571429 : Rat) / 2000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((6215896503774451 : Rat) / 500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((502058858928571429 : Rat) / 2000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((9498370268139933 : Rat) / 2000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((478919487053571429 : Rat) / 2000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((4613818283455279 : Rat) / 500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((467349801116071429 : Rat) / 2000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((316383417888437 : Rat) / 50000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((455780115178571429 : Rat) / 2000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((18754071017786783 : Rat) / 5000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((444210429241071429 : Rat) / 2000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((15126744872090703 : Rat) / 10000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((432640743303571429 : Rat) / 2000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((2502416619316883 : Rat) / 500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((426855900334821429 : Rat) / 2000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((4183849024805231 : Rat) / 1000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((421071057366071429 : Rat) / 2000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((6920305316335973 : Rat) / 2000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((415286214397321429 : Rat) / 2000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((2836839051914869 : Rat) / 1000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((409501371428571429 : Rat) / 2000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((5793140030515287 : Rat) / 2500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((403716528459821429 : Rat) / 2000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((19050333098165617 : Rat) / 10000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((397931685491071429 : Rat) / 2000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((2005145422192163 : Rat) / 1250000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((392146842522321429 : Rat) / 2000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((7094026357772759 : Rat) / 5000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((386361999553571429 : Rat) / 2000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((6769004362762593 : Rat) / 5000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((380577156584821429 : Rat) / 2000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((14142583629561667 : Rat) / 10000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((374792313616071429 : Rat) / 2000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((3211702354005641 : Rat) / 2000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((369007470647321429 : Rat) / 2000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((19348468855260037 : Rat) / 10000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((363222627678571429 : Rat) / 2000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((12040991225811537 : Rat) / 5000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((357437784709821429 : Rat) / 2000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((30336531997810223 : Rat) / 10000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((351652941741071429 : Rat) / 2000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((9549722123808821 : Rat) / 2500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((345868098772321429 : Rat) / 2000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((1194169008176857 : Rat) / 250000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((340083255803571429 : Rat) / 2000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((8458659828267101 : Rat) / 10000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((328513569866071429 : Rat) / 2000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((9388142466302679 : Rat) / 2500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((316943883928571429 : Rat) / 2000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((7569071151857121 : Rat) / 1000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((305374197991071429 : Rat) / 2000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((12460206539692181 : Rat) / 1000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((293804512053571429 : Rat) / 2000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1772854084556319 : Rat) / 200000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((270665140178571429 : Rat) / 2000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((3990685362349783 : Rat) / 500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((41151346396428571429 : Rat) / 16000000000000000000), D0 := ((41151346396428571429 : Rat) / 16000000000000000000), D1 := ((12071744796428571429 : Rat) / 16000000000000000000), D2 := ((224386396428571429 : Rat) / 16000000000000000000), D3 := ((224386396428571429 : Rat) / 2000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((10049006090012741 : Rat) / 200000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((41151346396428571429 : Rat) / 16000000000000000000), R := ((20687866396428571429 : Rat) / 8000000000000000000), D0 := ((20687866396428571429 : Rat) / 8000000000000000000), D1 := ((6148065596428571429 : Rat) / 8000000000000000000), D2 := ((224386396428571429 : Rat) / 8000000000000000000), D3 := ((1570704775000000003 : Rat) / 16000000000000000000), D4 := ((80164391517857103059 : Rat) / 400000000000000000000), LB := ((2952551817377809 : Rat) / 125000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((20687866396428571429 : Rat) / 8000000000000000000), R := ((41600119189285714287 : Rat) / 16000000000000000000), D0 := ((41600119189285714287 : Rat) / 16000000000000000000), D1 := ((12520517589285714287 : Rat) / 16000000000000000000), D2 := ((673159189285714287 : Rat) / 16000000000000000000), D3 := ((673159189285714287 : Rat) / 8000000000000000000), D4 := ((37277365803571408667 : Rat) / 200000000000000000000), LB := ((7324986650263529 : Rat) / 500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((41600119189285714287 : Rat) / 16000000000000000000), R := ((10456126396428571429 : Rat) / 4000000000000000000), D0 := ((10456126396428571429 : Rat) / 4000000000000000000), D1 := ((3186225996428571429 : Rat) / 4000000000000000000), D2 := ((224386396428571429 : Rat) / 4000000000000000000), D3 := ((224386396428571429 : Rat) / 3200000000000000000), D4 := ((68945071696428531609 : Rat) / 400000000000000000000), LB := ((16479926339337397 : Rat) / 1000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((10456126396428571429 : Rat) / 4000000000000000000), R := ((8409778396428571429 : Rat) / 3200000000000000000), D0 := ((8409778396428571429 : Rat) / 3200000000000000000), D1 := ((2593858076428571429 : Rat) / 3200000000000000000), D2 := ((224386396428571429 : Rat) / 3200000000000000000), D3 := ((224386396428571429 : Rat) / 4000000000000000000), D4 := ((15833852946428561471 : Rat) / 100000000000000000000), LB := ((3569388707053589 : Rat) / 125000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8409778396428571429 : Rat) / 3200000000000000000), R := ((21136639189285714287 : Rat) / 8000000000000000000), D0 := ((21136639189285714287 : Rat) / 8000000000000000000), D1 := ((6596838389285714287 : Rat) / 8000000000000000000), D2 := ((673159189285714287 : Rat) / 8000000000000000000), D3 := ((673159189285714287 : Rat) / 16000000000000000000), D4 := ((57725751874999960159 : Rat) / 400000000000000000000), LB := ((333574391108421 : Rat) / 6250000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21136639189285714287 : Rat) / 8000000000000000000), R := ((5340256396428571429 : Rat) / 2000000000000000000), D0 := ((5340256396428571429 : Rat) / 2000000000000000000), D1 := ((1705306196428571429 : Rat) / 2000000000000000000), D2 := ((224386396428571429 : Rat) / 2000000000000000000), D3 := ((224386396428571429 : Rat) / 8000000000000000000), D4 := ((26058045982142837217 : Rat) / 200000000000000000000), LB := ((1782529443570871 : Rat) / 25000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((5340256396428571429 : Rat) / 2000000000000000000), R := ((269039703035714285803 : Rat) / 100000000000000000000), D0 := ((269039703035714285803 : Rat) / 100000000000000000000), D1 := ((87292193035714285803 : Rat) / 100000000000000000000), D2 := ((13246203035714285803 : Rat) / 100000000000000000000), D3 := ((2026883214285714353 : Rat) / 100000000000000000000), D4 := ((5112096517857137873 : Rat) / 50000000000000000000), LB := ((5737257109121427 : Rat) / 50000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((269039703035714285803 : Rat) / 100000000000000000000), R := ((67766646562500000039 : Rat) / 25000000000000000000), D0 := ((67766646562500000039 : Rat) / 25000000000000000000), D1 := ((22329769062500000039 : Rat) / 25000000000000000000), D2 := ((3818271562500000039 : Rat) / 25000000000000000000), D3 := ((2026883214285714353 : Rat) / 50000000000000000000), D4 := ((8197309821428561393 : Rat) / 100000000000000000000), LB := ((8364223681163963 : Rat) / 1000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((67766646562500000039 : Rat) / 25000000000000000000), R := ((1086293228214285714977 : Rat) / 400000000000000000000), D0 := ((1086293228214285714977 : Rat) / 400000000000000000000), D1 := ((359303188214285714977 : Rat) / 400000000000000000000), D2 := ((63119228214285714977 : Rat) / 400000000000000000000), D3 := ((18241948928571429177 : Rat) / 400000000000000000000), D4 := ((19282583147321397 : Rat) / 312500000000000000), LB := ((5383389767704999 : Rat) / 250000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1086293228214285714977 : Rat) / 400000000000000000000), R := ((108832011142857142933 : Rat) / 40000000000000000000), D0 := ((108832011142857142933 : Rat) / 40000000000000000000), D1 := ((36133007142857142933 : Rat) / 40000000000000000000), D2 := ((6514611142857142933 : Rat) / 40000000000000000000), D3 := ((2026883214285714353 : Rat) / 40000000000000000000), D4 := ((22654823214285673807 : Rat) / 400000000000000000000), LB := ((9341797984602163 : Rat) / 1000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((108832011142857142933 : Rat) / 40000000000000000000), R := ((2178667106071428573013 : Rat) / 800000000000000000000), D0 := ((2178667106071428573013 : Rat) / 800000000000000000000), D1 := ((724687026071428573013 : Rat) / 800000000000000000000), D2 := ((132319106071428573013 : Rat) / 800000000000000000000), D3 := ((42564547500000001413 : Rat) / 800000000000000000000), D4 := ((10313969999999979727 : Rat) / 200000000000000000000), LB := ((10835114009224323 : Rat) / 1000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2178667106071428573013 : Rat) / 800000000000000000000), R := ((1090346994642857143683 : Rat) / 400000000000000000000), D0 := ((1090346994642857143683 : Rat) / 400000000000000000000), D1 := ((363356954642857143683 : Rat) / 400000000000000000000), D2 := ((67172994642857143683 : Rat) / 400000000000000000000), D3 := ((22295715357142857883 : Rat) / 400000000000000000000), D4 := ((7845799357142840911 : Rat) / 160000000000000000000), LB := ((3361115203323939 : Rat) / 500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1090346994642857143683 : Rat) / 400000000000000000000), R := ((2182720872500000001719 : Rat) / 800000000000000000000), D0 := ((2182720872500000001719 : Rat) / 800000000000000000000), D1 := ((728740792500000001719 : Rat) / 800000000000000000000), D2 := ((136372872500000001719 : Rat) / 800000000000000000000), D3 := ((46618313928571430119 : Rat) / 800000000000000000000), D4 := ((18601056785714245101 : Rat) / 400000000000000000000), LB := ((8243446603017901 : Rat) / 2500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2182720872500000001719 : Rat) / 800000000000000000000), R := ((273093469464285714509 : Rat) / 100000000000000000000), D0 := ((273093469464285714509 : Rat) / 100000000000000000000), D1 := ((91345959464285714509 : Rat) / 100000000000000000000), D2 := ((17299969464285714509 : Rat) / 100000000000000000000), D3 := ((6080649642857143059 : Rat) / 100000000000000000000), D4 := ((35175230357142775849 : Rat) / 800000000000000000000), LB := ((5756775101990463 : Rat) / 10000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((273093469464285714509 : Rat) / 100000000000000000000), R := ((4371522394642857146497 : Rat) / 1600000000000000000000), D0 := ((4371522394642857146497 : Rat) / 1600000000000000000000), D1 := ((1463562234642857146497 : Rat) / 1600000000000000000000), D2 := ((278826394642857146497 : Rat) / 1600000000000000000000), D3 := ((99317277500000003297 : Rat) / 1600000000000000000000), D4 := ((4143543392857132687 : Rat) / 100000000000000000000), LB := ((14157338911007 : Rat) / 3906250000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4371522394642857146497 : Rat) / 1600000000000000000000), R := ((87470985557142857217 : Rat) / 32000000000000000000), D0 := ((87470985557142857217 : Rat) / 32000000000000000000), D1 := ((29311782357142857217 : Rat) / 32000000000000000000), D2 := ((5617065557142857217 : Rat) / 32000000000000000000), D3 := ((2026883214285714353 : Rat) / 32000000000000000000), D4 := ((64269811071428408639 : Rat) / 1600000000000000000000), LB := ((1424727399382153 : Rat) / 500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87470985557142857217 : Rat) / 32000000000000000000), R := ((4375576161071428575203 : Rat) / 1600000000000000000000), D0 := ((4375576161071428575203 : Rat) / 1600000000000000000000), D1 := ((1467616001071428575203 : Rat) / 1600000000000000000000), D2 := ((282880161071428575203 : Rat) / 1600000000000000000000), D3 := ((103371043928571432003 : Rat) / 1600000000000000000000), D4 := ((31121463928571347143 : Rat) / 800000000000000000000), LB := ((22742139702195963 : Rat) / 10000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4375576161071428575203 : Rat) / 1600000000000000000000), R := ((1094400761071428572389 : Rat) / 400000000000000000000), D0 := ((1094400761071428572389 : Rat) / 400000000000000000000), D1 := ((367410721071428572389 : Rat) / 400000000000000000000), D2 := ((71226761071428572389 : Rat) / 400000000000000000000), D3 := ((26349481785714286589 : Rat) / 400000000000000000000), D4 := ((60216044642856979933 : Rat) / 1600000000000000000000), LB := ((4763259260802677 : Rat) / 2500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094400761071428572389 : Rat) / 400000000000000000000), R := ((4379629927500000003909 : Rat) / 1600000000000000000000), D0 := ((4379629927500000003909 : Rat) / 1600000000000000000000), D1 := ((1471669767500000003909 : Rat) / 1600000000000000000000), D2 := ((286933927500000003909 : Rat) / 1600000000000000000000), D3 := ((107424810357142860709 : Rat) / 1600000000000000000000), D4 := ((2909458071428563279 : Rat) / 80000000000000000000), LB := ((17505322007329571 : Rat) / 10000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4379629927500000003909 : Rat) / 1600000000000000000000), R := ((2190828405357142859131 : Rat) / 800000000000000000000), D0 := ((2190828405357142859131 : Rat) / 800000000000000000000), D1 := ((736848325357142859131 : Rat) / 800000000000000000000), D2 := ((144480405357142859131 : Rat) / 800000000000000000000), D3 := ((54725846785714287531 : Rat) / 800000000000000000000), D4 := ((56162278214285551227 : Rat) / 1600000000000000000000), LB := ((113680669709737 : Rat) / 62500000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2190828405357142859131 : Rat) / 800000000000000000000), R := ((876736738785714286523 : Rat) / 320000000000000000000), D0 := ((876736738785714286523 : Rat) / 320000000000000000000), D1 := ((295144706785714286523 : Rat) / 320000000000000000000), D2 := ((58197538785714286523 : Rat) / 320000000000000000000), D3 := ((22295715357142857883 : Rat) / 320000000000000000000), D4 := ((27067697499999918437 : Rat) / 800000000000000000000), LB := ((10603505033962013 : Rat) / 5000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((876736738785714286523 : Rat) / 320000000000000000000), R := ((548213822142857143371 : Rat) / 200000000000000000000), D0 := ((548213822142857143371 : Rat) / 200000000000000000000), D1 := ((184718802142857143371 : Rat) / 200000000000000000000), D2 := ((36626822142857143371 : Rat) / 200000000000000000000), D3 := ((14188182500000000471 : Rat) / 200000000000000000000), D4 := ((52108511785714122521 : Rat) / 1600000000000000000000), LB := ((533558681644597 : Rat) / 200000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((548213822142857143371 : Rat) / 200000000000000000000), R := ((4387737460357142861321 : Rat) / 1600000000000000000000), D0 := ((4387737460357142861321 : Rat) / 1600000000000000000000), D1 := ((1479777300357142861321 : Rat) / 1600000000000000000000), D2 := ((295041460357142861321 : Rat) / 1600000000000000000000), D3 := ((115532343214285718121 : Rat) / 1600000000000000000000), D4 := ((6260203571428551021 : Rat) / 200000000000000000000), LB := ((868430636501133 : Rat) / 250000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4387737460357142861321 : Rat) / 1600000000000000000000), R := ((2194882171785714287837 : Rat) / 800000000000000000000), D0 := ((2194882171785714287837 : Rat) / 800000000000000000000), D1 := ((740902091785714287837 : Rat) / 800000000000000000000), D2 := ((148534171785714287837 : Rat) / 800000000000000000000), D3 := ((58779613214285716237 : Rat) / 800000000000000000000), D4 := ((9610949071428538763 : Rat) / 320000000000000000000), LB := ((4554029792504577 : Rat) / 1000000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2194882171785714287837 : Rat) / 800000000000000000000), R := ((219690905500000000219 : Rat) / 80000000000000000000), D0 := ((219690905500000000219 : Rat) / 80000000000000000000), D1 := ((74292897500000000219 : Rat) / 80000000000000000000), D2 := ((15056105500000000219 : Rat) / 80000000000000000000), D3 := ((6080649642857143059 : Rat) / 80000000000000000000), D4 := ((23013931071428489731 : Rat) / 800000000000000000000), LB := ((3558581314829501 : Rat) / 2500000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((219690905500000000219 : Rat) / 80000000000000000000), R := ((2198935938214285716543 : Rat) / 800000000000000000000), D0 := ((2198935938214285716543 : Rat) / 800000000000000000000), D1 := ((744955858214285716543 : Rat) / 800000000000000000000), D2 := ((152587938214285716543 : Rat) / 800000000000000000000), D3 := ((62833379642857144943 : Rat) / 800000000000000000000), D4 := ((10493523928571387689 : Rat) / 400000000000000000000), LB := ((2087398672531271 : Rat) / 400000000000000000) },
  { w1 := ((2324108056861463 : Rat) / 2500000000000000), w2 := ((236941227765127 : Rat) / 5000000000000000), w3 := ((14592990817425333 : Rat) / 100000000000000000), w4 := ((1717675700033993 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5340256396428571429 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2198935938214285716543 : Rat) / 800000000000000000000), R := ((137560176339285714431 : Rat) / 50000000000000000000), D0 := ((137560176339285714431 : Rat) / 50000000000000000000), D1 := ((46686421339285714431 : Rat) / 50000000000000000000), D2 := ((9663426339285714431 : Rat) / 50000000000000000000), D3 := ((2026883214285714353 : Rat) / 25000000000000000000), D4 := ((758406585714282441 : Rat) / 32000000000000000000), LB := ((2093859098706119 : Rat) / 200000000000000000) }
]

def block339RightChunk000L : Rat := ((4377520089285714293 : Rat) / 2500000000000000000)
def block339RightChunk000R : Rat := ((137560176339285714431 : Rat) / 50000000000000000000)

def block339RightChunk000Certificate : Bool :=
  allBoxesValid block339RightChunk000 &&
  coversFromBool block339RightChunk000 block339RightChunk000L block339RightChunk000R

theorem block339RightChunk000Certificate_eq_true :
    block339RightChunk000Certificate = true := by
  native_decide

def block339RightChainCertificate : Bool :=
  decide (
    block339RightL = ((4377520089285714293 : Rat) / 2500000000000000000) /\
    ((137560176339285714431 : Rat) / 50000000000000000000) = block339RightR)

theorem block339RightChainCertificate_eq_true :
    block339RightChainCertificate = true := by
  native_decide

def block339LeftBoxCount : Nat := boxCount block339LeftBoxes
def block339RightBoxCount : Nat := 63

def block339_rational_certificate : Prop :=
    block339LeftCertificate = true /\
    block339RightChainCertificate = true /\
    block339RightChunk000Certificate = true

theorem block339_rational_certificate_proof :
    block339_rational_certificate := by
  exact ⟨block339LeftCertificate_eq_true, block339RightChainCertificate_eq_true, block339RightChunk000Certificate_eq_true⟩

end Block339
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block339

open Set

def block339W1 : Rat := ((2324108056861463 : Rat) / 2500000000000000)
def block339W2 : Rat := ((236941227765127 : Rat) / 5000000000000000)
def block339W3 : Rat := ((14592990817425333 : Rat) / 100000000000000000)
def block339W4 : Rat := ((1717675700033993 : Rat) / 12500000000000000)
def block339S1 : Rat := ((18174751 : Rat) / 10000000)
def block339S2 : Rat := ((511587 : Rat) / 200000)
def block339S3 : Rat := ((5340256396428571429 : Rat) / 2000000000000000000)
def block339S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block339V (y : ℝ) : ℝ :=
  ratPotential block339W1 block339W2 block339W3 block339W4 block339S1 block339S2 block339S3 block339S4 y

def block339LeftParamsCertificate : Bool :=
  allBoxesSameParams block339LeftBoxes block339W1 block339W2 block339W3 block339W4 block339S1 block339S2 block339S3 block339S4

theorem block339LeftParamsCertificate_eq_true :
    block339LeftParamsCertificate = true := by
  native_decide

theorem block339_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block339LeftL : ℝ) (block339LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block339S1 : ℝ))
    (hy2ne : y ≠ (block339S2 : ℝ))
    (hy3ne : y ≠ (block339S3 : ℝ))
    (hy4ne : y ≠ (block339S4 : ℝ)) :
    0 < block339V y := by
  have hcert := block339LeftCertificate_eq_true
  unfold block339LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block339LeftBoxes) (lo := block339LeftL) (hi := block339LeftR)
    (w1 := block339W1) (w2 := block339W2) (w3 := block339W3) (w4 := block339W4)
    (s1 := block339S1) (s2 := block339S2) (s3 := block339S3) (s4 := block339S4)
    hboxes hcover block339LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block339RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block339RightChunk000 block339W1 block339W2 block339W3 block339W4 block339S1 block339S2 block339S3 block339S4

theorem block339RightChunk000ParamsCertificate_eq_true :
    block339RightChunk000ParamsCertificate = true := by
  native_decide

theorem block339_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block339RightChunk000L : ℝ) (block339RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block339S1 : ℝ))
    (hy2ne : y ≠ (block339S2 : ℝ))
    (hy3ne : y ≠ (block339S3 : ℝ))
    (hy4ne : y ≠ (block339S4 : ℝ)) :
    0 < block339V y := by
  have hcert := block339RightChunk000Certificate_eq_true
  unfold block339RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block339RightChunk000) (lo := block339RightChunk000L) (hi := block339RightChunk000R)
    (w1 := block339W1) (w2 := block339W2) (w3 := block339W3) (w4 := block339W4)
    (s1 := block339S1) (s2 := block339S2) (s3 := block339S3) (s4 := block339S4)
    hboxes hcover block339RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block339_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block339RightL : ℝ) (block339RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block339S1 : ℝ))
    (hy2ne : y ≠ (block339S2 : ℝ))
    (hy3ne : y ≠ (block339S3 : ℝ))
    (hy4ne : y ≠ (block339S4 : ℝ)) :
    0 < block339V y := by
  have hL : (block339RightChunk000L : ℝ) = (block339RightL : ℝ) := by
    norm_num [block339RightChunk000L, block339RightL]
  have hR : (block339RightChunk000R : ℝ) = (block339RightR : ℝ) := by
    norm_num [block339RightChunk000R, block339RightR]
  have hyc : y ∈ Icc (block339RightChunk000L : ℝ) (block339RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block339_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block339_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block339LeftL : ℝ) (block339LeftR : ℝ) →
    y ≠ 0 → y ≠ (block339S1 : ℝ) → y ≠ (block339S2 : ℝ) →
    y ≠ (block339S3 : ℝ) → y ≠ (block339S4 : ℝ) → 0 < block339V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block339RightL : ℝ) (block339RightR : ℝ) →
    y ≠ 0 → y ≠ (block339S1 : ℝ) → y ≠ (block339S2 : ℝ) →
    y ≠ (block339S3 : ℝ) → y ≠ (block339S4 : ℝ) → 0 < block339V y)

theorem block339_reallog_certificate_proof :
    block339_reallog_certificate := by
  exact ⟨block339_left_V_pos, block339_right_V_pos⟩

end Block339
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block339.block339V
#check Erdos1038Lean.M1817475.Block339.block339_left_V_pos
#check Erdos1038Lean.M1817475.Block339.block339_right_V_pos
#check Erdos1038Lean.M1817475.Block339.block339_reallog_certificate_proof
