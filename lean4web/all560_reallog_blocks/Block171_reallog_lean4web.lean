/-
Self-contained Lean4Web paste file.
Block 171 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block171

def block171LeftL : Rat := ((9798131696428571447 : Rat) / 12500000000000000000)
def block171LeftR : Rat := ((39202301339285714359 : Rat) / 50000000000000000000)
def block171RightL : Rat := ((22298131696428571447 : Rat) / 12500000000000000000)
def block171RightR : Rat := ((139202301339285714359 : Rat) / 50000000000000000000)

def block171LeftBoxes : List RatBox := [
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9798131696428571447 : Rat) / 12500000000000000000), R := ((39202301339285714359 : Rat) / 50000000000000000000), D0 := ((39202301339285714359 : Rat) / 50000000000000000000), D1 := ((12920307053571428553 : Rat) / 12500000000000000000), D2 := ((22176055803571428553 : Rat) / 12500000000000000000), D3 := ((96855267053571428397 : Rat) / 50000000000000000000), D4 := ((25008000491071427303 : Rat) / 12500000000000000000), LB := ((1221573595827077 : Rat) / 625000000000000000) }
]

def block171LeftCertificate : Bool :=
  allBoxesValid block171LeftBoxes &&
  coversFromBool block171LeftBoxes block171LeftL block171LeftR

theorem block171LeftCertificate_eq_true :
    block171LeftCertificate = true := by
  native_decide

def block171RightChunk000 : List RatBox := [
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((22298131696428571447 : Rat) / 12500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((420307053571428553 : Rat) / 12500000000000000000), D2 := ((9676055803571428553 : Rat) / 12500000000000000000), D3 := ((46855267053571428397 : Rat) / 50000000000000000000), D4 := ((12508000491071427303 : Rat) / 12500000000000000000), LB := ((1397267185373787 : Rat) / 250000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((104639033859717 : Rat) / 100000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((72881277440741 : Rat) / 200000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((1546827731854517 : Rat) / 10000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((275470347268491 : Rat) / 3125000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((450581392009701 : Rat) / 250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((1043083615150403 : Rat) / 200000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((1127012000465763 : Rat) / 125000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((3158805878241397 : Rat) / 250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((61086322624999968141 : Rat) / 320000000000000000000), LB := ((8014763668584557 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((3816687151264153 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((6690146753596249 : Rat) / 100000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((180029464117 : Rat) / 50000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((4268587897688303 : Rat) / 2000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((8003871802191309 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((2984787909253439 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((3043480191751019 : Rat) / 1250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((384226379018493 : Rat) / 200000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((1805690249461131 : Rat) / 1250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((628620608470673 : Rat) / 625000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((6056303036978961 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((612174702056753 : Rat) / 2500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((7999338456539107 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((405549933839285460441 : Rat) / 2560000000000000000000), LB := ((14537810379840477 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((1318084681249887 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((1192892708746729 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((2156642952245269 : Rat) / 2000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((2436224168626891 : Rat) / 2500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((2203795894303029 : Rat) / 2500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((3997655387264487 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((728653879552621 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((6690154084779687 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((3103734859183499 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((116796522899959 : Rat) / 200000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((558859195347039 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((272758233380091 : Rat) / 500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((5440971569800057 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((221898822181521 : Rat) / 400000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((5776151013017483 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((6128534750529657 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((1651544234443289 : Rat) / 2500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((5633333670253 : Rat) / 7812500000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((1588726026165721 : Rat) / 2000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((8806727376215739 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((4900828858828421 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((10930158729133 : Rat) / 10000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((6097003933177303 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((6797511852372623 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((3783766806629979 : Rat) / 2500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((8408021579568159 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((11050630796828609 : Rat) / 50000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((3158624783983627 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((220408537045641 : Rat) / 200000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((16337037910038321 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((11142669876608169 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((3393162040053571427101 : Rat) / 1280000000000000000000), D0 := ((3393162040053571427101 : Rat) / 1280000000000000000000), D1 := ((1066793912053571427101 : Rat) / 1280000000000000000000), D2 := ((119005240053571427101 : Rat) / 1280000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((14442263567720631 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3393162040053571427101 : Rat) / 1280000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 256000000000000000000), D4 := ((170985895946428444899 : Rat) / 1280000000000000000000), LB := ((3615479857371151 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((5803318863272233 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((29788646222984327 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((5102541623983103 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((11173403401996407 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((1784208435561041 : Rat) / 250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((8280853913597 : Rat) / 3906250000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((430462313982142856881 : Rat) / 160000000000000000000), D0 := ((430462313982142856881 : Rat) / 160000000000000000000), D1 := ((139666297982142856881 : Rat) / 160000000000000000000), D2 := ((21192713982142856881 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((298472615828577 : Rat) / 12500000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((430462313982142856881 : Rat) / 160000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 160000000000000000000), D4 := ((15056178017857127119 : Rat) / 160000000000000000000), LB := ((11543604846977601 : Rat) / 200000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((8841300775476549 : Rat) / 100000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((273672841428571428457 : Rat) / 100000000000000000000), D0 := ((273672841428571428457 : Rat) / 100000000000000000000), D1 := ((91925331428571428457 : Rat) / 100000000000000000000), D2 := ((17879341428571428457 : Rat) / 100000000000000000000), D3 := ((1577253750000000087 : Rat) / 100000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((3056539361061017 : Rat) / 25000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((273672841428571428457 : Rat) / 100000000000000000000), R := ((548922936607142857001 : Rat) / 200000000000000000000), D0 := ((548922936607142857001 : Rat) / 200000000000000000000), D1 := ((185427916607142857001 : Rat) / 200000000000000000000), D2 := ((37335936607142857001 : Rat) / 200000000000000000000), D3 := ((4731761250000000261 : Rat) / 200000000000000000000), D4 := ((4776216071428561543 : Rat) / 100000000000000000000), LB := ((3221732333620031 : Rat) / 50000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((548922936607142857001 : Rat) / 200000000000000000000), R := ((4300782737165178571 : Rat) / 1562500000000000000), D0 := ((4300782737165178571 : Rat) / 1562500000000000000), D1 := ((1460977893415178571 : Rat) / 1562500000000000000), D2 := ((304009299665178571 : Rat) / 1562500000000000000), D3 := ((1577253750000000087 : Rat) / 50000000000000000000), D4 := ((7975178392857122999 : Rat) / 200000000000000000000), LB := ((998304269712081 : Rat) / 62500000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4300782737165178571 : Rat) / 1562500000000000000), R := ((1102577634464285714263 : Rat) / 400000000000000000000), D0 := ((1102577634464285714263 : Rat) / 400000000000000000000), D1 := ((375587594464285714263 : Rat) / 400000000000000000000), D2 := ((79403634464285714263 : Rat) / 400000000000000000000), D3 := ((14195283750000000783 : Rat) / 400000000000000000000), D4 := ((199935145089285091 : Rat) / 6250000000000000000), LB := ((9300877534717089 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1102577634464285714263 : Rat) / 400000000000000000000), R := ((2206732522678571428613 : Rat) / 800000000000000000000), D0 := ((2206732522678571428613 : Rat) / 800000000000000000000), D1 := ((752752442678571428613 : Rat) / 800000000000000000000), D2 := ((160384522678571428613 : Rat) / 800000000000000000000), D3 := ((29967821250000001653 : Rat) / 800000000000000000000), D4 := ((11218595535714245737 : Rat) / 400000000000000000000), LB := ((4472093080841233 : Rat) / 500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2206732522678571428613 : Rat) / 800000000000000000000), R := ((22083097764285714287 : Rat) / 8000000000000000000), D0 := ((22083097764285714287 : Rat) / 8000000000000000000), D1 := ((7543296964285714287 : Rat) / 8000000000000000000), D2 := ((1619617764285714287 : Rat) / 8000000000000000000), D3 := ((1577253750000000087 : Rat) / 40000000000000000000), D4 := ((20859937321428491387 : Rat) / 800000000000000000000), LB := ((15729727327405407 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((22083097764285714287 : Rat) / 8000000000000000000), R := ((4418196806607142857487 : Rat) / 1600000000000000000000), D0 := ((4418196806607142857487 : Rat) / 1600000000000000000000), D1 := ((1510236646607142857487 : Rat) / 1600000000000000000000), D2 := ((325500806607142857487 : Rat) / 1600000000000000000000), D3 := ((64667403750000003567 : Rat) / 1600000000000000000000), D4 := ((192826835714284913 : Rat) / 8000000000000000000), LB := ((233233289191509 : Rat) / 50000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4418196806607142857487 : Rat) / 1600000000000000000000), R := ((2209887030178571428787 : Rat) / 800000000000000000000), D0 := ((2209887030178571428787 : Rat) / 800000000000000000000), D1 := ((755906950178571428787 : Rat) / 800000000000000000000), D2 := ((163539030178571428787 : Rat) / 800000000000000000000), D3 := ((33122328750000001827 : Rat) / 800000000000000000000), D4 := ((36988113392856982513 : Rat) / 1600000000000000000000), LB := ((3209055120986723 : Rat) / 1250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2209887030178571428787 : Rat) / 800000000000000000000), R := ((4421351314107142857661 : Rat) / 1600000000000000000000), D0 := ((4421351314107142857661 : Rat) / 1600000000000000000000), D1 := ((1513391154107142857661 : Rat) / 1600000000000000000000), D2 := ((328655314107142857661 : Rat) / 1600000000000000000000), D3 := ((67821911250000003741 : Rat) / 1600000000000000000000), D4 := ((17705429821428491213 : Rat) / 800000000000000000000), LB := ((117321075411847 : Rat) / 156250000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4421351314107142857661 : Rat) / 1600000000000000000000), R := ((8844279881964285715409 : Rat) / 3200000000000000000000), D0 := ((8844279881964285715409 : Rat) / 3200000000000000000000), D1 := ((3028359561964285715409 : Rat) / 3200000000000000000000), D2 := ((658887881964285715409 : Rat) / 3200000000000000000000), D3 := ((137221076250000007569 : Rat) / 3200000000000000000000), D4 := ((33833605892856982339 : Rat) / 1600000000000000000000), LB := ((11379185567905181 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8844279881964285715409 : Rat) / 3200000000000000000000), R := ((1105732141964285714437 : Rat) / 400000000000000000000), D0 := ((1105732141964285714437 : Rat) / 400000000000000000000), D1 := ((378742101964285714437 : Rat) / 400000000000000000000), D2 := ((82558141964285714437 : Rat) / 400000000000000000000), D3 := ((17349791250000000957 : Rat) / 400000000000000000000), D4 := ((66089958035713964591 : Rat) / 3200000000000000000000), LB := ((16066862223630407 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1105732141964285714437 : Rat) / 400000000000000000000), R := ((8847434389464285715583 : Rat) / 3200000000000000000000), D0 := ((8847434389464285715583 : Rat) / 3200000000000000000000), D1 := ((3031514069464285715583 : Rat) / 3200000000000000000000), D2 := ((662042389464285715583 : Rat) / 3200000000000000000000), D3 := ((140375583750000007743 : Rat) / 3200000000000000000000), D4 := ((8064088035714245563 : Rat) / 400000000000000000000), LB := ((2034472363362183 : Rat) / 2000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8847434389464285715583 : Rat) / 3200000000000000000000), R := ((884901164321428571567 : Rat) / 320000000000000000000), D0 := ((884901164321428571567 : Rat) / 320000000000000000000), D1 := ((303309132321428571567 : Rat) / 320000000000000000000), D2 := ((66361964321428571567 : Rat) / 320000000000000000000), D3 := ((14195283750000000783 : Rat) / 320000000000000000000), D4 := ((62935450535713964417 : Rat) / 3200000000000000000000), LB := ((637306196045323 : Rat) / 1250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((884901164321428571567 : Rat) / 320000000000000000000), R := ((8850588896964285715757 : Rat) / 3200000000000000000000), D0 := ((8850588896964285715757 : Rat) / 3200000000000000000000), D1 := ((3034668576964285715757 : Rat) / 3200000000000000000000), D2 := ((665196896964285715757 : Rat) / 3200000000000000000000), D3 := ((143530091250000007917 : Rat) / 3200000000000000000000), D4 := ((6135819678571396433 : Rat) / 320000000000000000000), LB := ((217756979772471 : Rat) / 2500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8850588896964285715757 : Rat) / 3200000000000000000000), R := ((17702755047678571431601 : Rat) / 6400000000000000000000), D0 := ((17702755047678571431601 : Rat) / 6400000000000000000000), D1 := ((6070914407678571431601 : Rat) / 6400000000000000000000), D2 := ((1331971047678571431601 : Rat) / 6400000000000000000000), D3 := ((288637436250000015921 : Rat) / 6400000000000000000000), D4 := ((59780943035713964243 : Rat) / 3200000000000000000000), LB := ((6151098164432489 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17702755047678571431601 : Rat) / 6400000000000000000000), R := ((2213041537678571428961 : Rat) / 800000000000000000000), D0 := ((2213041537678571428961 : Rat) / 800000000000000000000), D1 := ((759061457678571428961 : Rat) / 800000000000000000000), D2 := ((166693537678571428961 : Rat) / 800000000000000000000), D3 := ((36276836250000002001 : Rat) / 800000000000000000000), D4 := ((117984632321427928399 : Rat) / 6400000000000000000000), LB := ((2182543555332317 : Rat) / 2000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2213041537678571428961 : Rat) / 800000000000000000000), R := ((708236382207142857271 : Rat) / 256000000000000000000), D0 := ((708236382207142857271 : Rat) / 256000000000000000000), D1 := ((242962756607142857271 : Rat) / 256000000000000000000), D2 := ((53405022207142857271 : Rat) / 256000000000000000000), D3 := ((58358388750000003219 : Rat) / 1280000000000000000000), D4 := ((14550922321428491039 : Rat) / 800000000000000000000), LB := ((9754451832144073 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((708236382207142857271 : Rat) / 256000000000000000000), R := ((8853743404464285715931 : Rat) / 3200000000000000000000), D0 := ((8853743404464285715931 : Rat) / 3200000000000000000000), D1 := ((3037823084464285715931 : Rat) / 3200000000000000000000), D2 := ((668351404464285715931 : Rat) / 3200000000000000000000), D3 := ((146684598750000008091 : Rat) / 3200000000000000000000), D4 := ((4593204992857117129 : Rat) / 256000000000000000000), LB := ((8831774956613581 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8853743404464285715931 : Rat) / 3200000000000000000000), R := ((17709064062678571431949 : Rat) / 6400000000000000000000), D0 := ((17709064062678571431949 : Rat) / 6400000000000000000000), D1 := ((6077223422678571431949 : Rat) / 6400000000000000000000), D2 := ((1338280062678571431949 : Rat) / 6400000000000000000000), D3 := ((294946451250000016269 : Rat) / 6400000000000000000000), D4 := ((56626435535713964069 : Rat) / 3200000000000000000000), LB := ((1629855049460227 : Rat) / 2000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17709064062678571431949 : Rat) / 6400000000000000000000), R := ((4427660329107142858009 : Rat) / 1600000000000000000000), D0 := ((4427660329107142858009 : Rat) / 1600000000000000000000), D1 := ((1519700169107142858009 : Rat) / 1600000000000000000000), D2 := ((334964329107142858009 : Rat) / 1600000000000000000000), D3 := ((74130926250000004089 : Rat) / 1600000000000000000000), D4 := ((111675617321427928051 : Rat) / 6400000000000000000000), LB := ((963970438792941 : Rat) / 1250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4427660329107142858009 : Rat) / 1600000000000000000000), R := ((17712218570178571432123 : Rat) / 6400000000000000000000), D0 := ((17712218570178571432123 : Rat) / 6400000000000000000000), D1 := ((6080377930178571432123 : Rat) / 6400000000000000000000), D2 := ((1341434570178571432123 : Rat) / 6400000000000000000000), D3 := ((298100958750000016443 : Rat) / 6400000000000000000000), D4 := ((27524590892856981991 : Rat) / 1600000000000000000000), LB := ((1881071279441343 : Rat) / 2500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17712218570178571432123 : Rat) / 6400000000000000000000), R := ((1771379582392857143221 : Rat) / 640000000000000000000), D0 := ((1771379582392857143221 : Rat) / 640000000000000000000), D1 := ((608195518392857143221 : Rat) / 640000000000000000000), D2 := ((134301182392857143221 : Rat) / 640000000000000000000), D3 := ((29967821250000001653 : Rat) / 640000000000000000000), D4 := ((108521109821427927877 : Rat) / 6400000000000000000000), LB := ((75921327121653 : Rat) / 100000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1771379582392857143221 : Rat) / 640000000000000000000), R := ((17715373077678571432297 : Rat) / 6400000000000000000000), D0 := ((17715373077678571432297 : Rat) / 6400000000000000000000), D1 := ((6083532437678571432297 : Rat) / 6400000000000000000000), D2 := ((1344589077678571432297 : Rat) / 6400000000000000000000), D3 := ((301255466250000016617 : Rat) / 6400000000000000000000), D4 := ((10694385607142792779 : Rat) / 640000000000000000000), LB := ((7920859829158577 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17715373077678571432297 : Rat) / 6400000000000000000000), R := ((276827348928571428631 : Rat) / 100000000000000000000), D0 := ((276827348928571428631 : Rat) / 100000000000000000000), D1 := ((95079838928571428631 : Rat) / 100000000000000000000), D2 := ((21033848928571428631 : Rat) / 100000000000000000000), D3 := ((4731761250000000261 : Rat) / 100000000000000000000), D4 := ((105366602321427927703 : Rat) / 6400000000000000000000), LB := ((2129073878458787 : Rat) / 2500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((276827348928571428631 : Rat) / 100000000000000000000), R := ((17718527585178571432471 : Rat) / 6400000000000000000000), D0 := ((17718527585178571432471 : Rat) / 6400000000000000000000), D1 := ((6086686945178571432471 : Rat) / 6400000000000000000000), D2 := ((1347743585178571432471 : Rat) / 6400000000000000000000), D3 := ((304409973750000016791 : Rat) / 6400000000000000000000), D4 := ((1621708571428561369 : Rat) / 100000000000000000000), LB := ((2346140003761793 : Rat) / 2500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17718527585178571432471 : Rat) / 6400000000000000000000), R := ((8860052419464285716279 : Rat) / 3200000000000000000000), D0 := ((8860052419464285716279 : Rat) / 3200000000000000000000), D1 := ((3044132099464285716279 : Rat) / 3200000000000000000000), D2 := ((674660419464285716279 : Rat) / 3200000000000000000000), D3 := ((152993613750000008439 : Rat) / 3200000000000000000000), D4 := ((102212094821427927529 : Rat) / 6400000000000000000000), LB := ((5266040824710161 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8860052419464285716279 : Rat) / 3200000000000000000000), R := ((3544336418535714286529 : Rat) / 1280000000000000000000), D0 := ((3544336418535714286529 : Rat) / 1280000000000000000000), D1 := ((1217968290535714286529 : Rat) / 1280000000000000000000), D2 := ((270179618535714286529 : Rat) / 1280000000000000000000), D3 := ((61512896250000003393 : Rat) / 1280000000000000000000), D4 := ((50317420535713963721 : Rat) / 3200000000000000000000), LB := ((11965614935828817 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3544336418535714286529 : Rat) / 1280000000000000000000), R := ((4430814836607142858183 : Rat) / 1600000000000000000000), D0 := ((4430814836607142858183 : Rat) / 1600000000000000000000), D1 := ((1522854676607142858183 : Rat) / 1600000000000000000000), D2 := ((338118836607142858183 : Rat) / 1600000000000000000000), D3 := ((77285433750000004263 : Rat) / 1600000000000000000000), D4 := ((19811517464285585471 : Rat) / 1280000000000000000000), LB := ((6846130055412347 : Rat) / 5000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4430814836607142858183 : Rat) / 1600000000000000000000), R := ((8863206926964285716453 : Rat) / 3200000000000000000000), D0 := ((8863206926964285716453 : Rat) / 3200000000000000000000), D1 := ((3047286606964285716453 : Rat) / 3200000000000000000000), D2 := ((677814926964285716453 : Rat) / 3200000000000000000000), D3 := ((156148121250000008613 : Rat) / 3200000000000000000000), D4 := ((24370083392856981817 : Rat) / 1600000000000000000000), LB := ((1603667385146057 : Rat) / 10000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8863206926964285716453 : Rat) / 3200000000000000000000), R := ((443239209035714285827 : Rat) / 160000000000000000000), D0 := ((443239209035714285827 : Rat) / 160000000000000000000), D1 := ((152443193035714285827 : Rat) / 160000000000000000000), D2 := ((33969609035714285827 : Rat) / 160000000000000000000), D3 := ((1577253750000000087 : Rat) / 32000000000000000000), D4 := ((47162913035713963547 : Rat) / 3200000000000000000000), LB := ((1335928832805977 : Rat) / 2000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((443239209035714285827 : Rat) / 160000000000000000000), R := ((8866361434464285716627 : Rat) / 3200000000000000000000), D0 := ((8866361434464285716627 : Rat) / 3200000000000000000000), D1 := ((3050441114464285716627 : Rat) / 3200000000000000000000), D2 := ((680969434464285716627 : Rat) / 3200000000000000000000), D3 := ((159302628750000008787 : Rat) / 3200000000000000000000), D4 := ((2279282964285698173 : Rat) / 160000000000000000000), LB := ((652802797439539 : Rat) / 500000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8866361434464285716627 : Rat) / 3200000000000000000000), R := ((4433969344107142858357 : Rat) / 1600000000000000000000), D0 := ((4433969344107142858357 : Rat) / 1600000000000000000000), D1 := ((1526009184107142858357 : Rat) / 1600000000000000000000), D2 := ((341273344107142858357 : Rat) / 1600000000000000000000), D3 := ((80439941250000004437 : Rat) / 1600000000000000000000), D4 := ((44008405535713963373 : Rat) / 3200000000000000000000), LB := ((2080844815647631 : Rat) / 1000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4433969344107142858357 : Rat) / 1600000000000000000000), R := ((1108886649464285714611 : Rat) / 400000000000000000000), D0 := ((1108886649464285714611 : Rat) / 400000000000000000000), D1 := ((381896609464285714611 : Rat) / 400000000000000000000), D2 := ((85712649464285714611 : Rat) / 400000000000000000000), D3 := ((20504298750000001131 : Rat) / 400000000000000000000), D4 := ((21215575892856981643 : Rat) / 1600000000000000000000), LB := ((12976553786669953 : Rat) / 50000000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1108886649464285714611 : Rat) / 400000000000000000000), R := ((4437123851607142858531 : Rat) / 1600000000000000000000), D0 := ((4437123851607142858531 : Rat) / 1600000000000000000000), D1 := ((1529163691607142858531 : Rat) / 1600000000000000000000), D2 := ((344427851607142858531 : Rat) / 1600000000000000000000), D3 := ((83594448750000004611 : Rat) / 1600000000000000000000), D4 := ((4909580535714245389 : Rat) / 400000000000000000000), LB := ((26105380382794863 : Rat) / 10000000000000000000) }
]

def block171RightChunk000L : Rat := ((22298131696428571447 : Rat) / 12500000000000000000)
def block171RightChunk000R : Rat := ((4437123851607142858531 : Rat) / 1600000000000000000000)

def block171RightChunk000Certificate : Bool :=
  allBoxesValid block171RightChunk000 &&
  coversFromBool block171RightChunk000 block171RightChunk000L block171RightChunk000R

theorem block171RightChunk000Certificate_eq_true :
    block171RightChunk000Certificate = true := by
  native_decide

def block171RightChunk001 : List RatBox := [
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4437123851607142858531 : Rat) / 1600000000000000000000), R := ((2219350552678571429309 : Rat) / 800000000000000000000), D0 := ((2219350552678571429309 : Rat) / 800000000000000000000), D1 := ((765370472678571429309 : Rat) / 800000000000000000000), D2 := ((173002552678571429309 : Rat) / 800000000000000000000), D3 := ((42585851250000002349 : Rat) / 800000000000000000000), D4 := ((18061068392856981469 : Rat) / 1600000000000000000000), LB := ((1418156438202381 : Rat) / 250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2219350552678571429309 : Rat) / 800000000000000000000), R := ((555231951607142857349 : Rat) / 200000000000000000000), D0 := ((555231951607142857349 : Rat) / 200000000000000000000), D1 := ((191736931607142857349 : Rat) / 200000000000000000000), D2 := ((43644951607142857349 : Rat) / 200000000000000000000), D3 := ((11040776250000000609 : Rat) / 200000000000000000000), D4 := ((8241907321428490691 : Rat) / 800000000000000000000), LB := ((1075399209325853 : Rat) / 250000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((555231951607142857349 : Rat) / 200000000000000000000), R := ((222408231392857142957 : Rat) / 80000000000000000000), D0 := ((222408231392857142957 : Rat) / 80000000000000000000), D1 := ((77010223392857142957 : Rat) / 80000000000000000000), D2 := ((17773431392857142957 : Rat) / 80000000000000000000), D3 := ((4731761250000000261 : Rat) / 80000000000000000000), D4 := ((1666163392857122651 : Rat) / 200000000000000000000), LB := ((102936953384003 : Rat) / 20000000000000000) },
  { w1 := ((113774152801223 : Rat) / 62500000000000), w2 := (0 : Rat), w3 := ((2101962447137189 : Rat) / 12500000000000000), w4 := ((10086329484976389 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((222408231392857142957 : Rat) / 80000000000000000000), R := ((139202301339285714359 : Rat) / 50000000000000000000), D0 := ((139202301339285714359 : Rat) / 50000000000000000000), D1 := ((48328546339285714359 : Rat) / 50000000000000000000), D2 := ((11305551339285714359 : Rat) / 50000000000000000000), D3 := ((1577253750000000087 : Rat) / 25000000000000000000), D4 := ((351014607142849043 : Rat) / 80000000000000000000), LB := ((4810906381235519 : Rat) / 100000000000000000) }
]

def block171RightChunk001L : Rat := ((4437123851607142858531 : Rat) / 1600000000000000000000)
def block171RightChunk001R : Rat := ((139202301339285714359 : Rat) / 50000000000000000000)

def block171RightChunk001Certificate : Bool :=
  allBoxesValid block171RightChunk001 &&
  coversFromBool block171RightChunk001 block171RightChunk001L block171RightChunk001R

theorem block171RightChunk001Certificate_eq_true :
    block171RightChunk001Certificate = true := by
  native_decide

def block171RightChainCertificate : Bool :=
  decide (
    block171RightL = ((22298131696428571447 : Rat) / 12500000000000000000) /\
    ((4437123851607142858531 : Rat) / 1600000000000000000000) = ((4437123851607142858531 : Rat) / 1600000000000000000000) /\
    ((139202301339285714359 : Rat) / 50000000000000000000) = block171RightR)

theorem block171RightChainCertificate_eq_true :
    block171RightChainCertificate = true := by
  native_decide

def block171LeftBoxCount : Nat := boxCount block171LeftBoxes
def block171RightBoxCount : Nat := 104

def block171_rational_certificate : Prop :=
    block171LeftCertificate = true /\
    block171RightChainCertificate = true /\
    block171RightChunk000Certificate = true /\
    block171RightChunk001Certificate = true

theorem block171_rational_certificate_proof :
    block171_rational_certificate := by
  exact ⟨block171LeftCertificate_eq_true, block171RightChainCertificate_eq_true, block171RightChunk000Certificate_eq_true, block171RightChunk001Certificate_eq_true⟩

end Block171
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block171

open Set

def block171W1 : Rat := ((113774152801223 : Rat) / 62500000000000)
def block171W2 : Rat := (0 : Rat)
def block171W3 : Rat := ((2101962447137189 : Rat) / 12500000000000000)
def block171W4 : Rat := ((10086329484976389 : Rat) / 100000000000000000)
def block171S1 : Rat := ((18174751 : Rat) / 10000000)
def block171S2 : Rat := ((511587 : Rat) / 200000)
def block171S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block171S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block171V (y : ℝ) : ℝ :=
  ratPotential block171W1 block171W2 block171W3 block171W4 block171S1 block171S2 block171S3 block171S4 y

def block171LeftParamsCertificate : Bool :=
  allBoxesSameParams block171LeftBoxes block171W1 block171W2 block171W3 block171W4 block171S1 block171S2 block171S3 block171S4

theorem block171LeftParamsCertificate_eq_true :
    block171LeftParamsCertificate = true := by
  native_decide

theorem block171_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block171LeftL : ℝ) (block171LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block171S1 : ℝ))
    (hy2ne : y ≠ (block171S2 : ℝ))
    (hy3ne : y ≠ (block171S3 : ℝ))
    (hy4ne : y ≠ (block171S4 : ℝ)) :
    0 < block171V y := by
  have hcert := block171LeftCertificate_eq_true
  unfold block171LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block171LeftBoxes) (lo := block171LeftL) (hi := block171LeftR)
    (w1 := block171W1) (w2 := block171W2) (w3 := block171W3) (w4 := block171W4)
    (s1 := block171S1) (s2 := block171S2) (s3 := block171S3) (s4 := block171S4)
    hboxes hcover block171LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block171RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block171RightChunk000 block171W1 block171W2 block171W3 block171W4 block171S1 block171S2 block171S3 block171S4

theorem block171RightChunk000ParamsCertificate_eq_true :
    block171RightChunk000ParamsCertificate = true := by
  native_decide

theorem block171_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block171RightChunk000L : ℝ) (block171RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block171S1 : ℝ))
    (hy2ne : y ≠ (block171S2 : ℝ))
    (hy3ne : y ≠ (block171S3 : ℝ))
    (hy4ne : y ≠ (block171S4 : ℝ)) :
    0 < block171V y := by
  have hcert := block171RightChunk000Certificate_eq_true
  unfold block171RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block171RightChunk000) (lo := block171RightChunk000L) (hi := block171RightChunk000R)
    (w1 := block171W1) (w2 := block171W2) (w3 := block171W3) (w4 := block171W4)
    (s1 := block171S1) (s2 := block171S2) (s3 := block171S3) (s4 := block171S4)
    hboxes hcover block171RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block171RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block171RightChunk001 block171W1 block171W2 block171W3 block171W4 block171S1 block171S2 block171S3 block171S4

theorem block171RightChunk001ParamsCertificate_eq_true :
    block171RightChunk001ParamsCertificate = true := by
  native_decide

theorem block171_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block171RightChunk001L : ℝ) (block171RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block171S1 : ℝ))
    (hy2ne : y ≠ (block171S2 : ℝ))
    (hy3ne : y ≠ (block171S3 : ℝ))
    (hy4ne : y ≠ (block171S4 : ℝ)) :
    0 < block171V y := by
  have hcert := block171RightChunk001Certificate_eq_true
  unfold block171RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block171RightChunk001) (lo := block171RightChunk001L) (hi := block171RightChunk001R)
    (w1 := block171W1) (w2 := block171W2) (w3 := block171W3) (w4 := block171W4)
    (s1 := block171S1) (s2 := block171S2) (s3 := block171S3) (s4 := block171S4)
    hboxes hcover block171RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block171_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block171RightL : ℝ) (block171RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block171S1 : ℝ))
    (hy2ne : y ≠ (block171S2 : ℝ))
    (hy3ne : y ≠ (block171S3 : ℝ))
    (hy4ne : y ≠ (block171S4 : ℝ)) :
    0 < block171V y := by
  by_cases h0 : y ≤ (block171RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block171RightChunk000L : ℝ) (block171RightChunk000R : ℝ) := by
      have hL : (block171RightChunk000L : ℝ) = (block171RightL : ℝ) := by
        norm_num [block171RightChunk000L, block171RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block171_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block171RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block171RightChunk001L : ℝ) = (block171RightChunk000R : ℝ) := by
      norm_num [block171RightChunk001L, block171RightChunk000R]
    have hR : (block171RightChunk001R : ℝ) = (block171RightR : ℝ) := by
      norm_num [block171RightChunk001R, block171RightR]
    have hyc : y ∈ Icc (block171RightChunk001L : ℝ) (block171RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block171_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block171_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block171LeftL : ℝ) (block171LeftR : ℝ) →
    y ≠ 0 → y ≠ (block171S1 : ℝ) → y ≠ (block171S2 : ℝ) →
    y ≠ (block171S3 : ℝ) → y ≠ (block171S4 : ℝ) → 0 < block171V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block171RightL : ℝ) (block171RightR : ℝ) →
    y ≠ 0 → y ≠ (block171S1 : ℝ) → y ≠ (block171S2 : ℝ) →
    y ≠ (block171S3 : ℝ) → y ≠ (block171S4 : ℝ) → 0 < block171V y)

theorem block171_reallog_certificate_proof :
    block171_reallog_certificate := by
  exact ⟨block171_left_V_pos, block171_right_V_pos⟩

end Block171
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block171.block171V
#check Erdos1038Lean.M1817475.Block171.block171_left_V_pos
#check Erdos1038Lean.M1817475.Block171.block171_right_V_pos
#check Erdos1038Lean.M1817475.Block171.block171_reallog_certificate_proof
