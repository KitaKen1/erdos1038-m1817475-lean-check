/-
Self-contained Lean4Web paste file.
Block 172 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block172

def block172LeftL : Rat := ((39182752232142857217 : Rat) / 50000000000000000000)
def block172LeftR : Rat := ((9798131696428571447 : Rat) / 12500000000000000000)
def block172RightL : Rat := ((89182752232142857217 : Rat) / 50000000000000000000)
def block172RightR : Rat := ((34798131696428571447 : Rat) / 12500000000000000000)

def block172LeftBoxes : List RatBox := [
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((39182752232142857217 : Rat) / 50000000000000000000), R := ((9798131696428571447 : Rat) / 12500000000000000000), D0 := ((9798131696428571447 : Rat) / 12500000000000000000), D1 := ((51691002767857142783 : Rat) / 50000000000000000000), D2 := ((88713997767857142783 : Rat) / 50000000000000000000), D3 := ((12108130200892857121 : Rat) / 6250000000000000000), D4 := ((100041776517857137783 : Rat) / 50000000000000000000), LB := ((1856966060576351 : Rat) / 1000000000000000000) }
]

def block172LeftCertificate : Bool :=
  allBoxesValid block172LeftBoxes &&
  coversFromBool block172LeftBoxes block172LeftL block172LeftR

theorem block172LeftCertificate_eq_true :
    block172LeftCertificate = true := by
  native_decide

def block172RightChunk000 : List RatBox := [
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((89182752232142857217 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1691002767857142783 : Rat) / 50000000000000000000), D2 := ((38713997767857142783 : Rat) / 50000000000000000000), D3 := ((5858130200892857121 : Rat) / 6250000000000000000), D4 := ((50041776517857137783 : Rat) / 50000000000000000000), LB := ((2781329309800507 : Rat) / 500000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((1041799349398023 : Rat) / 1000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((361856750137183 : Rat) / 1000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((3824526868790929 : Rat) / 25000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((1085891100992639 : Rat) / 12500000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((2234685086535959 : Rat) / 2500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((9050987521476539 : Rat) / 2000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((1055010825287861 : Rat) / 125000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((48478379639183 : Rat) / 4000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((61086322624999968141 : Rat) / 320000000000000000000), LB := ((294752608395939 : Rat) / 39062500000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((33947710995523017 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((1630791385088419 : Rat) / 250000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((114021601410714222097 : Rat) / 640000000000000000000), LB := ((1931959554398599 : Rat) / 400000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((6520692252422411 : Rat) / 2000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((1818821166874679 : Rat) / 1000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((2549683130698699 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((27121851816138687 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((21749451553809973 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((4185326809184181 : Rat) / 2500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((12104654608246501 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((7846998842749031 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((397612798510083 : Rat) / 1000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((5001272515495203 : Rat) / 100000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((3536434113919143 : Rat) / 2500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((405549933839285460441 : Rat) / 2560000000000000000000), LB := ((12751477727697413 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((11461352845715533 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((1027650673965791 : Rat) / 1000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((4599053553709931 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((8227345021579457 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((1473087111382887 : Rat) / 2000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((6613618439220981 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((5973158716701399 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((5445347454494653 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((5031502453664571 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((4732968995454223 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((455112061196139 : Rat) / 1000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((5609199855519803 : Rat) / 12500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((45431192702319323 : Rat) / 100000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((4719861960079397 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((1003816553256709 : Rat) / 2000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((1088461808817609 : Rat) / 2000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((5991101646978803 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((1666763979490879 : Rat) / 2500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((3735901359054883 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((4203504747138237 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((947438138779011 : Rat) / 1000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((10675662385887519 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((750789782383611 : Rat) / 625000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((674356454985453 : Rat) / 500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((3775252005991589 : Rat) / 2500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((16856185106661203 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((23608970935165563 : Rat) / 100000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((827282809900097 : Rat) / 1250000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((5736633051355161 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((1694335329484653 : Rat) / 1000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((11523425049289743 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((3393162040053571427101 : Rat) / 1280000000000000000000), D0 := ((3393162040053571427101 : Rat) / 1280000000000000000000), D1 := ((1066793912053571427101 : Rat) / 1280000000000000000000), D2 := ((119005240053571427101 : Rat) / 1280000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((298030241590741 : Rat) / 100000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3393162040053571427101 : Rat) / 1280000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 256000000000000000000), D4 := ((170985895946428444899 : Rat) / 1280000000000000000000), LB := ((3723215103209193 : Rat) / 1000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((12916054771348329 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((31425659509326243 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((5299893359857477 : Rat) / 1000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((2726818790870833 : Rat) / 2000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((1491079870803913 : Rat) / 200000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((12719698830527537 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((430462313982142856881 : Rat) / 160000000000000000000), D0 := ((430462313982142856881 : Rat) / 160000000000000000000), D1 := ((139666297982142856881 : Rat) / 160000000000000000000), D2 := ((21192713982142856881 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((305979134006093 : Rat) / 12500000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((430462313982142856881 : Rat) / 160000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 160000000000000000000), D4 := ((15056178017857127119 : Rat) / 160000000000000000000), LB := ((5853905043009289 : Rat) / 100000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((8959164005098891 : Rat) / 100000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((547335908303571428343 : Rat) / 200000000000000000000), D0 := ((547335908303571428343 : Rat) / 200000000000000000000), D1 := ((183840888303571428343 : Rat) / 200000000000000000000), D2 := ((35748908303571428343 : Rat) / 200000000000000000000), D3 := ((3144732946428571603 : Rat) / 200000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((3105139024280451 : Rat) / 25000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((547335908303571428343 : Rat) / 200000000000000000000), R := ((1097816549553571428289 : Rat) / 400000000000000000000), D0 := ((1097816549553571428289 : Rat) / 400000000000000000000), D1 := ((370826509553571428289 : Rat) / 400000000000000000000), D2 := ((74642549553571428289 : Rat) / 400000000000000000000), D3 := ((9434198839285714809 : Rat) / 400000000000000000000), D4 := ((9562206696428551657 : Rat) / 200000000000000000000), LB := ((131804088249861 : Rat) / 2000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1097816549553571428289 : Rat) / 400000000000000000000), R := ((275240320624999999973 : Rat) / 100000000000000000000), D0 := ((275240320624999999973 : Rat) / 100000000000000000000), D1 := ((93492810624999999973 : Rat) / 100000000000000000000), D2 := ((19446820624999999973 : Rat) / 100000000000000000000), D3 := ((3144732946428571603 : Rat) / 100000000000000000000), D4 := ((15979680446428531711 : Rat) / 400000000000000000000), LB := ((8565971442390241 : Rat) / 500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((275240320624999999973 : Rat) / 100000000000000000000), R := ((2205067297946428571387 : Rat) / 800000000000000000000), D0 := ((2205067297946428571387 : Rat) / 800000000000000000000), D1 := ((751087217946428571387 : Rat) / 800000000000000000000), D2 := ((158719297946428571387 : Rat) / 800000000000000000000), D3 := ((28302596517857144427 : Rat) / 800000000000000000000), D4 := ((3208736874999990027 : Rat) / 100000000000000000000), LB := ((254331406315611 : Rat) / 25000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2205067297946428571387 : Rat) / 800000000000000000000), R := ((4413279328839285714377 : Rat) / 1600000000000000000000), D0 := ((4413279328839285714377 : Rat) / 1600000000000000000000), D1 := ((1505319168839285714377 : Rat) / 1600000000000000000000), D2 := ((320583328839285714377 : Rat) / 1600000000000000000000), D3 := ((59749925982142860457 : Rat) / 1600000000000000000000), D4 := ((22525162053571348613 : Rat) / 800000000000000000000), LB := ((602471226106481 : Rat) / 62500000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4413279328839285714377 : Rat) / 1600000000000000000000), R := ((220821203089285714299 : Rat) / 80000000000000000000), D0 := ((220821203089285714299 : Rat) / 80000000000000000000), D1 := ((75423195089285714299 : Rat) / 80000000000000000000), D2 := ((16186403089285714299 : Rat) / 80000000000000000000), D3 := ((3144732946428571603 : Rat) / 80000000000000000000), D4 := ((41905591160714125623 : Rat) / 1600000000000000000000), LB := ((2332472321409651 : Rat) / 625000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((220821203089285714299 : Rat) / 80000000000000000000), R := ((8835992856517857143563 : Rat) / 3200000000000000000000), D0 := ((8835992856517857143563 : Rat) / 3200000000000000000000), D1 := ((3020072536517857143563 : Rat) / 3200000000000000000000), D2 := ((650600856517857143563 : Rat) / 3200000000000000000000), D3 := ((128934050803571435723 : Rat) / 3200000000000000000000), D4 := ((1938042910714277701 : Rat) / 80000000000000000000), LB := ((5138461927128191 : Rat) / 1000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8835992856517857143563 : Rat) / 3200000000000000000000), R := ((4419568794732142857583 : Rat) / 1600000000000000000000), D0 := ((4419568794732142857583 : Rat) / 1600000000000000000000), D1 := ((1511608634732142857583 : Rat) / 1600000000000000000000), D2 := ((326872794732142857583 : Rat) / 1600000000000000000000), D3 := ((66039391875000003663 : Rat) / 1600000000000000000000), D4 := ((74376983482142536437 : Rat) / 3200000000000000000000), LB := ((14881828870430547 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4419568794732142857583 : Rat) / 1600000000000000000000), R := ((8842282322410714286769 : Rat) / 3200000000000000000000), D0 := ((8842282322410714286769 : Rat) / 3200000000000000000000), D1 := ((3026362002410714286769 : Rat) / 3200000000000000000000), D2 := ((656890322410714286769 : Rat) / 3200000000000000000000), D3 := ((135223516696428578929 : Rat) / 3200000000000000000000), D4 := ((35616125267856982417 : Rat) / 1600000000000000000000), LB := ((2183287620856289 : Rat) / 2000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8842282322410714286769 : Rat) / 3200000000000000000000), R := ((17687709377767857145141 : Rat) / 6400000000000000000000), D0 := ((17687709377767857145141 : Rat) / 6400000000000000000000), D1 := ((6055868737767857145141 : Rat) / 6400000000000000000000), D2 := ((1316925377767857145141 : Rat) / 6400000000000000000000), D3 := ((273591766339285729461 : Rat) / 6400000000000000000000), D4 := ((68087517589285393231 : Rat) / 3200000000000000000000), LB := ((318394589790931 : Rat) / 125000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17687709377767857145141 : Rat) / 6400000000000000000000), R := ((2211356763839285714593 : Rat) / 800000000000000000000), D0 := ((2211356763839285714593 : Rat) / 800000000000000000000), D1 := ((757376683839285714593 : Rat) / 800000000000000000000), D2 := ((165008763839285714593 : Rat) / 800000000000000000000), D3 := ((34592062410714287633 : Rat) / 800000000000000000000), D4 := ((133030302232142214859 : Rat) / 6400000000000000000000), LB := ((3679752912850831 : Rat) / 2000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2211356763839285714593 : Rat) / 800000000000000000000), R := ((17693998843660714288347 : Rat) / 6400000000000000000000), D0 := ((17693998843660714288347 : Rat) / 6400000000000000000000), D1 := ((6062158203660714288347 : Rat) / 6400000000000000000000), D2 := ((1323214843660714288347 : Rat) / 6400000000000000000000), D3 := ((279881232232142872667 : Rat) / 6400000000000000000000), D4 := ((16235696160714205407 : Rat) / 800000000000000000000), LB := ((6055015067521763 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17693998843660714288347 : Rat) / 6400000000000000000000), R := ((353942871532142857199 : Rat) / 128000000000000000000), D0 := ((353942871532142857199 : Rat) / 128000000000000000000), D1 := ((121306058732142857199 : Rat) / 128000000000000000000), D2 := ((26527191532142857199 : Rat) / 128000000000000000000), D3 := ((28302596517857144427 : Rat) / 640000000000000000000), D4 := ((126740836339285071653 : Rat) / 6400000000000000000000), LB := ((414247605129113 : Rat) / 625000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((353942871532142857199 : Rat) / 128000000000000000000), R := ((17700288309553571431553 : Rat) / 6400000000000000000000), D0 := ((17700288309553571431553 : Rat) / 6400000000000000000000), D1 := ((6068447669553571431553 : Rat) / 6400000000000000000000), D2 := ((1329504309553571431553 : Rat) / 6400000000000000000000), D3 := ((286170698125000015873 : Rat) / 6400000000000000000000), D4 := ((2471922067857130001 : Rat) / 128000000000000000000), LB := ((617933357769003 : Rat) / 3125000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17700288309553571431553 : Rat) / 6400000000000000000000), R := ((35403721352053571434709 : Rat) / 12800000000000000000000), D0 := ((35403721352053571434709 : Rat) / 12800000000000000000000), D1 := ((12140040072053571434709 : Rat) / 12800000000000000000000), D2 := ((2662153352053571434709 : Rat) / 12800000000000000000000), D3 := ((575486129196428603349 : Rat) / 12800000000000000000000), D4 := ((120451370446427928447 : Rat) / 6400000000000000000000), LB := ((6491288988098587 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35403721352053571434709 : Rat) / 12800000000000000000000), R := ((4425858260625000000789 : Rat) / 1600000000000000000000), D0 := ((4425858260625000000789 : Rat) / 1600000000000000000000), D1 := ((1517898100625000000789 : Rat) / 1600000000000000000000), D2 := ((333162260625000000789 : Rat) / 1600000000000000000000), D3 := ((72328857767857146869 : Rat) / 1600000000000000000000), D4 := ((237758007946427285291 : Rat) / 12800000000000000000000), LB := ((355210927211521 : Rat) / 312500000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4425858260625000000789 : Rat) / 1600000000000000000000), R := ((7082002163589285715583 : Rat) / 2560000000000000000000), D0 := ((7082002163589285715583 : Rat) / 2560000000000000000000), D1 := ((2429265907589285715583 : Rat) / 2560000000000000000000), D2 := ((533688563589285715583 : Rat) / 2560000000000000000000), D3 := ((116355119017857149311 : Rat) / 2560000000000000000000), D4 := ((29326659374999839211 : Rat) / 1600000000000000000000), LB := ((2494398791283159 : Rat) / 2500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7082002163589285715583 : Rat) / 2560000000000000000000), R := ((17706577775446428574759 : Rat) / 6400000000000000000000), D0 := ((17706577775446428574759 : Rat) / 6400000000000000000000), D1 := ((6074737135446428574759 : Rat) / 6400000000000000000000), D2 := ((1335793775446428574759 : Rat) / 6400000000000000000000), D3 := ((292460164017857159079 : Rat) / 6400000000000000000000), D4 := ((46293708410714028417 : Rat) / 2560000000000000000000), LB := ((4409653712519057 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17706577775446428574759 : Rat) / 6400000000000000000000), R := ((35416300283839285721121 : Rat) / 12800000000000000000000), D0 := ((35416300283839285721121 : Rat) / 12800000000000000000000), D1 := ((12152619003839285721121 : Rat) / 12800000000000000000000), D2 := ((2674732283839285721121 : Rat) / 12800000000000000000000), D3 := ((588065060982142889761 : Rat) / 12800000000000000000000), D4 := ((114161904553570785241 : Rat) / 6400000000000000000000), LB := ((493517594588877 : Rat) / 625000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35416300283839285721121 : Rat) / 12800000000000000000000), R := ((8854861254196428573181 : Rat) / 3200000000000000000000), D0 := ((8854861254196428573181 : Rat) / 3200000000000000000000), D1 := ((3038940934196428573181 : Rat) / 3200000000000000000000), D2 := ((669469254196428573181 : Rat) / 3200000000000000000000), D3 := ((147802448482142865341 : Rat) / 3200000000000000000000), D4 := ((225179076160712998879 : Rat) / 12800000000000000000000), LB := ((1803281254676159 : Rat) / 2500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8854861254196428573181 : Rat) / 3200000000000000000000), R := ((35422589749732142864327 : Rat) / 12800000000000000000000), D0 := ((35422589749732142864327 : Rat) / 12800000000000000000000), D1 := ((12158908469732142864327 : Rat) / 12800000000000000000000), D2 := ((2681021749732142864327 : Rat) / 12800000000000000000000), D3 := ((594354526875000032967 : Rat) / 12800000000000000000000), D4 := ((55508585803571106819 : Rat) / 3200000000000000000000), LB := ((3387334607735659 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35422589749732142864327 : Rat) / 12800000000000000000000), R := ((3542573448267857143593 : Rat) / 1280000000000000000000), D0 := ((3542573448267857143593 : Rat) / 1280000000000000000000), D1 := ((1216205320267857143593 : Rat) / 1280000000000000000000), D2 := ((268416648267857143593 : Rat) / 1280000000000000000000), D3 := ((59749925982142860457 : Rat) / 1280000000000000000000), D4 := ((218889610267855855673 : Rat) / 12800000000000000000000), LB := ((1317196203200477 : Rat) / 2000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3542573448267857143593 : Rat) / 1280000000000000000000), R := ((35428879215625000007533 : Rat) / 12800000000000000000000), D0 := ((35428879215625000007533 : Rat) / 12800000000000000000000), D1 := ((12165197935625000007533 : Rat) / 12800000000000000000000), D2 := ((2687311215625000007533 : Rat) / 12800000000000000000000), D3 := ((600643992767857176173 : Rat) / 12800000000000000000000), D4 := ((21574487732142728407 : Rat) / 1280000000000000000000), LB := ((6652375777547737 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35428879215625000007533 : Rat) / 12800000000000000000000), R := ((553625374196428571549 : Rat) / 200000000000000000000), D0 := ((553625374196428571549 : Rat) / 200000000000000000000), D1 := ((190130354196428571549 : Rat) / 200000000000000000000), D2 := ((42038374196428571549 : Rat) / 200000000000000000000), D3 := ((9434198839285714809 : Rat) / 200000000000000000000), D4 := ((212600144374998712467 : Rat) / 12800000000000000000000), LB := ((1744857758917001 : Rat) / 2500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553625374196428571549 : Rat) / 200000000000000000000), R := ((35435168681517857150739 : Rat) / 12800000000000000000000), D0 := ((35435168681517857150739 : Rat) / 12800000000000000000000), D1 := ((12171487401517857150739 : Rat) / 12800000000000000000000), D2 := ((2693600681517857150739 : Rat) / 12800000000000000000000), D3 := ((606933458660714319379 : Rat) / 12800000000000000000000), D4 := ((3272740803571408451 : Rat) / 200000000000000000000), LB := ((7573001241236721 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35435168681517857150739 : Rat) / 12800000000000000000000), R := ((17719156707232142861171 : Rat) / 6400000000000000000000), D0 := ((17719156707232142861171 : Rat) / 6400000000000000000000), D1 := ((6087316067232142861171 : Rat) / 6400000000000000000000), D2 := ((1348372707232142861171 : Rat) / 6400000000000000000000), D3 := ((305039095803571445491 : Rat) / 6400000000000000000000), D4 := ((206310678482141569261 : Rat) / 12800000000000000000000), LB := ((8439233585246231 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17719156707232142861171 : Rat) / 6400000000000000000000), R := ((7088291629482142858789 : Rat) / 2560000000000000000000), D0 := ((7088291629482142858789 : Rat) / 2560000000000000000000), D1 := ((2435555373482142858789 : Rat) / 2560000000000000000000), D2 := ((539978029482142858789 : Rat) / 2560000000000000000000), D3 := ((122644584910714292517 : Rat) / 2560000000000000000000), D4 := ((101582972767856498829 : Rat) / 6400000000000000000000), LB := ((9584585004845381 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7088291629482142858789 : Rat) / 2560000000000000000000), R := ((8861150720089285716387 : Rat) / 3200000000000000000000), D0 := ((8861150720089285716387 : Rat) / 3200000000000000000000), D1 := ((3045230400089285716387 : Rat) / 3200000000000000000000), D2 := ((675758720089285716387 : Rat) / 3200000000000000000000), D3 := ((154091914375000008547 : Rat) / 3200000000000000000000), D4 := ((40004242517856885211 : Rat) / 2560000000000000000000), LB := ((440633618880093 : Rat) / 400000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8861150720089285716387 : Rat) / 3200000000000000000000), R := ((35447747613303571437151 : Rat) / 12800000000000000000000), D0 := ((35447747613303571437151 : Rat) / 12800000000000000000000), D1 := ((12184066333303571437151 : Rat) / 12800000000000000000000), D2 := ((2706179613303571437151 : Rat) / 12800000000000000000000), D3 := ((619512390446428605791 : Rat) / 12800000000000000000000), D4 := ((49219119910713963613 : Rat) / 3200000000000000000000), LB := ((12740132676915539 : Rat) / 10000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35447747613303571437151 : Rat) / 12800000000000000000000), R := ((17725446173125000004377 : Rat) / 6400000000000000000000), D0 := ((17725446173125000004377 : Rat) / 6400000000000000000000), D1 := ((6093605533125000004377 : Rat) / 6400000000000000000000), D2 := ((1354662173125000004377 : Rat) / 6400000000000000000000), D3 := ((311328561696428588697 : Rat) / 6400000000000000000000), D4 := ((193731746696427282849 : Rat) / 12800000000000000000000), LB := ((369124080724037 : Rat) / 250000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17725446173125000004377 : Rat) / 6400000000000000000000), R := ((886429545303571428799 : Rat) / 320000000000000000000), D0 := ((886429545303571428799 : Rat) / 320000000000000000000), D1 := ((304837513303571428799 : Rat) / 320000000000000000000), D2 := ((67890345303571428799 : Rat) / 320000000000000000000), D3 := ((3144732946428571603 : Rat) / 64000000000000000000), D4 := ((95293506874999355623 : Rat) / 6400000000000000000000), LB := ((3825270082321447 : Rat) / 12500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((886429545303571428799 : Rat) / 320000000000000000000), R := ((17731735639017857147583 : Rat) / 6400000000000000000000), D0 := ((17731735639017857147583 : Rat) / 6400000000000000000000), D1 := ((6099894999017857147583 : Rat) / 6400000000000000000000), D2 := ((1360951639017857147583 : Rat) / 6400000000000000000000), D3 := ((317618027589285731903 : Rat) / 6400000000000000000000), D4 := ((4607438696428539201 : Rat) / 320000000000000000000), LB := ((10965421574647 : Rat) / 12500000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17731735639017857147583 : Rat) / 6400000000000000000000), R := ((8867440185982142859593 : Rat) / 3200000000000000000000), D0 := ((8867440185982142859593 : Rat) / 3200000000000000000000), D1 := ((3051519865982142859593 : Rat) / 3200000000000000000000), D2 := ((682048185982142859593 : Rat) / 3200000000000000000000), D3 := ((160381380267857151753 : Rat) / 3200000000000000000000), D4 := ((89004040982142212417 : Rat) / 6400000000000000000000), LB := ((395554577904203 : Rat) / 250000000000000000) }
]

def block172RightChunk000L : Rat := ((89182752232142857217 : Rat) / 50000000000000000000)
def block172RightChunk000R : Rat := ((8867440185982142859593 : Rat) / 3200000000000000000000)

def block172RightChunk000Certificate : Bool :=
  allBoxesValid block172RightChunk000 &&
  coversFromBool block172RightChunk000 block172RightChunk000L block172RightChunk000R

theorem block172RightChunk000Certificate_eq_true :
    block172RightChunk000Certificate = true := by
  native_decide

def block172RightChunk001 : List RatBox := [
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8867440185982142859593 : Rat) / 3200000000000000000000), R := ((17738025104910714290789 : Rat) / 6400000000000000000000), D0 := ((17738025104910714290789 : Rat) / 6400000000000000000000), D1 := ((6106184464910714290789 : Rat) / 6400000000000000000000), D2 := ((1367241104910714290789 : Rat) / 6400000000000000000000), D3 := ((323907493482142875109 : Rat) / 6400000000000000000000), D4 := ((42929654017856820407 : Rat) / 3200000000000000000000), LB := ((1214491967164999 : Rat) / 500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17738025104910714290789 : Rat) / 6400000000000000000000), R := ((2217646229732142857799 : Rat) / 800000000000000000000), D0 := ((2217646229732142857799 : Rat) / 800000000000000000000), D1 := ((763666149732142857799 : Rat) / 800000000000000000000), D2 := ((171298229732142857799 : Rat) / 800000000000000000000), D3 := ((40881528303571430839 : Rat) / 800000000000000000000), D4 := ((82714575089285069211 : Rat) / 6400000000000000000000), LB := ((8566145997541269 : Rat) / 2500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2217646229732142857799 : Rat) / 800000000000000000000), R := ((8873729651875000002799 : Rat) / 3200000000000000000000), D0 := ((8873729651875000002799 : Rat) / 3200000000000000000000), D1 := ((3057809331875000002799 : Rat) / 3200000000000000000000), D2 := ((688337651875000002799 : Rat) / 3200000000000000000000), D3 := ((166670846160714294959 : Rat) / 3200000000000000000000), D4 := ((9946230267857062201 : Rat) / 800000000000000000000), LB := ((9361318499634397 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8873729651875000002799 : Rat) / 3200000000000000000000), R := ((4438437192410714287201 : Rat) / 1600000000000000000000), D0 := ((4438437192410714287201 : Rat) / 1600000000000000000000), D1 := ((1530477032410714287201 : Rat) / 1600000000000000000000), D2 := ((345741192410714287201 : Rat) / 1600000000000000000000), D3 := ((84907789553571433281 : Rat) / 1600000000000000000000), D4 := ((36640188124999677201 : Rat) / 3200000000000000000000), LB := ((2373806246134147 : Rat) / 500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4438437192410714287201 : Rat) / 1600000000000000000000), R := ((1110395481339285714701 : Rat) / 400000000000000000000), D0 := ((1110395481339285714701 : Rat) / 400000000000000000000), D1 := ((383405441339285714701 : Rat) / 400000000000000000000), D2 := ((87221481339285714701 : Rat) / 400000000000000000000), D3 := ((22013130625000001221 : Rat) / 400000000000000000000), D4 := ((16747727589285552799 : Rat) / 1600000000000000000000), LB := ((1578938331380647 : Rat) / 500000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1110395481339285714701 : Rat) / 400000000000000000000), R := ((444787139125000000201 : Rat) / 160000000000000000000), D0 := ((444787139125000000201 : Rat) / 160000000000000000000), D1 := ((153991123125000000201 : Rat) / 160000000000000000000), D2 := ((35517539125000000201 : Rat) / 160000000000000000000), D3 := ((9434198839285714809 : Rat) / 160000000000000000000), D4 := ((3400748660714245299 : Rat) / 400000000000000000000), LB := ((17217693630298403 : Rat) / 5000000000000000000) },
  { w1 := ((18157055131371727 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16893042516110107 : Rat) / 100000000000000000), w4 := ((10031548731137031 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((444787139125000000201 : Rat) / 160000000000000000000), R := ((34798131696428571447 : Rat) / 12500000000000000000), D0 := ((34798131696428571447 : Rat) / 12500000000000000000), D1 := ((12079692946428571447 : Rat) / 12500000000000000000), D2 := ((2823944196428571447 : Rat) / 12500000000000000000), D3 := ((3144732946428571603 : Rat) / 50000000000000000000), D4 := ((731352874999983799 : Rat) / 160000000000000000000), LB := ((4426078842304143 : Rat) / 100000000000000000) }
]

def block172RightChunk001L : Rat := ((8867440185982142859593 : Rat) / 3200000000000000000000)
def block172RightChunk001R : Rat := ((34798131696428571447 : Rat) / 12500000000000000000)

def block172RightChunk001Certificate : Bool :=
  allBoxesValid block172RightChunk001 &&
  coversFromBool block172RightChunk001 block172RightChunk001L block172RightChunk001R

theorem block172RightChunk001Certificate_eq_true :
    block172RightChunk001Certificate = true := by
  native_decide

def block172RightChainCertificate : Bool :=
  decide (
    block172RightL = ((89182752232142857217 : Rat) / 50000000000000000000) /\
    ((8867440185982142859593 : Rat) / 3200000000000000000000) = ((8867440185982142859593 : Rat) / 3200000000000000000000) /\
    ((34798131696428571447 : Rat) / 12500000000000000000) = block172RightR)

theorem block172RightChainCertificate_eq_true :
    block172RightChainCertificate = true := by
  native_decide

def block172LeftBoxCount : Nat := boxCount block172LeftBoxes
def block172RightBoxCount : Nat := 107

def block172_rational_certificate : Prop :=
    block172LeftCertificate = true /\
    block172RightChainCertificate = true /\
    block172RightChunk000Certificate = true /\
    block172RightChunk001Certificate = true

theorem block172_rational_certificate_proof :
    block172_rational_certificate := by
  exact ⟨block172LeftCertificate_eq_true, block172RightChainCertificate_eq_true, block172RightChunk000Certificate_eq_true, block172RightChunk001Certificate_eq_true⟩

end Block172
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block172

open Set

def block172W1 : Rat := ((18157055131371727 : Rat) / 10000000000000000)
def block172W2 : Rat := (0 : Rat)
def block172W3 : Rat := ((16893042516110107 : Rat) / 100000000000000000)
def block172W4 : Rat := ((10031548731137031 : Rat) / 100000000000000000)
def block172S1 : Rat := ((18174751 : Rat) / 10000000)
def block172S2 : Rat := ((511587 : Rat) / 200000)
def block172S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block172S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block172V (y : ℝ) : ℝ :=
  ratPotential block172W1 block172W2 block172W3 block172W4 block172S1 block172S2 block172S3 block172S4 y

def block172LeftParamsCertificate : Bool :=
  allBoxesSameParams block172LeftBoxes block172W1 block172W2 block172W3 block172W4 block172S1 block172S2 block172S3 block172S4

theorem block172LeftParamsCertificate_eq_true :
    block172LeftParamsCertificate = true := by
  native_decide

theorem block172_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block172LeftL : ℝ) (block172LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block172S1 : ℝ))
    (hy2ne : y ≠ (block172S2 : ℝ))
    (hy3ne : y ≠ (block172S3 : ℝ))
    (hy4ne : y ≠ (block172S4 : ℝ)) :
    0 < block172V y := by
  have hcert := block172LeftCertificate_eq_true
  unfold block172LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block172LeftBoxes) (lo := block172LeftL) (hi := block172LeftR)
    (w1 := block172W1) (w2 := block172W2) (w3 := block172W3) (w4 := block172W4)
    (s1 := block172S1) (s2 := block172S2) (s3 := block172S3) (s4 := block172S4)
    hboxes hcover block172LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block172RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block172RightChunk000 block172W1 block172W2 block172W3 block172W4 block172S1 block172S2 block172S3 block172S4

theorem block172RightChunk000ParamsCertificate_eq_true :
    block172RightChunk000ParamsCertificate = true := by
  native_decide

theorem block172_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block172RightChunk000L : ℝ) (block172RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block172S1 : ℝ))
    (hy2ne : y ≠ (block172S2 : ℝ))
    (hy3ne : y ≠ (block172S3 : ℝ))
    (hy4ne : y ≠ (block172S4 : ℝ)) :
    0 < block172V y := by
  have hcert := block172RightChunk000Certificate_eq_true
  unfold block172RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block172RightChunk000) (lo := block172RightChunk000L) (hi := block172RightChunk000R)
    (w1 := block172W1) (w2 := block172W2) (w3 := block172W3) (w4 := block172W4)
    (s1 := block172S1) (s2 := block172S2) (s3 := block172S3) (s4 := block172S4)
    hboxes hcover block172RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block172RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block172RightChunk001 block172W1 block172W2 block172W3 block172W4 block172S1 block172S2 block172S3 block172S4

theorem block172RightChunk001ParamsCertificate_eq_true :
    block172RightChunk001ParamsCertificate = true := by
  native_decide

theorem block172_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block172RightChunk001L : ℝ) (block172RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block172S1 : ℝ))
    (hy2ne : y ≠ (block172S2 : ℝ))
    (hy3ne : y ≠ (block172S3 : ℝ))
    (hy4ne : y ≠ (block172S4 : ℝ)) :
    0 < block172V y := by
  have hcert := block172RightChunk001Certificate_eq_true
  unfold block172RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block172RightChunk001) (lo := block172RightChunk001L) (hi := block172RightChunk001R)
    (w1 := block172W1) (w2 := block172W2) (w3 := block172W3) (w4 := block172W4)
    (s1 := block172S1) (s2 := block172S2) (s3 := block172S3) (s4 := block172S4)
    hboxes hcover block172RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block172_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block172RightL : ℝ) (block172RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block172S1 : ℝ))
    (hy2ne : y ≠ (block172S2 : ℝ))
    (hy3ne : y ≠ (block172S3 : ℝ))
    (hy4ne : y ≠ (block172S4 : ℝ)) :
    0 < block172V y := by
  by_cases h0 : y ≤ (block172RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block172RightChunk000L : ℝ) (block172RightChunk000R : ℝ) := by
      have hL : (block172RightChunk000L : ℝ) = (block172RightL : ℝ) := by
        norm_num [block172RightChunk000L, block172RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block172_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block172RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block172RightChunk001L : ℝ) = (block172RightChunk000R : ℝ) := by
      norm_num [block172RightChunk001L, block172RightChunk000R]
    have hR : (block172RightChunk001R : ℝ) = (block172RightR : ℝ) := by
      norm_num [block172RightChunk001R, block172RightR]
    have hyc : y ∈ Icc (block172RightChunk001L : ℝ) (block172RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block172_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block172_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block172LeftL : ℝ) (block172LeftR : ℝ) →
    y ≠ 0 → y ≠ (block172S1 : ℝ) → y ≠ (block172S2 : ℝ) →
    y ≠ (block172S3 : ℝ) → y ≠ (block172S4 : ℝ) → 0 < block172V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block172RightL : ℝ) (block172RightR : ℝ) →
    y ≠ 0 → y ≠ (block172S1 : ℝ) → y ≠ (block172S2 : ℝ) →
    y ≠ (block172S3 : ℝ) → y ≠ (block172S4 : ℝ) → 0 < block172V y)

theorem block172_reallog_certificate_proof :
    block172_reallog_certificate := by
  exact ⟨block172_left_V_pos, block172_right_V_pos⟩

end Block172
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block172.block172V
#check Erdos1038Lean.M1817475.Block172.block172_left_V_pos
#check Erdos1038Lean.M1817475.Block172.block172_right_V_pos
#check Erdos1038Lean.M1817475.Block172.block172_reallog_certificate_proof
