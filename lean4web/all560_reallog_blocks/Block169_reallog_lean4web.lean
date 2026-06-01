/-
Self-contained Lean4Web paste file.
Block 169 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block169

def block169LeftL : Rat := ((3921207589285714293 : Rat) / 5000000000000000000)
def block169LeftR : Rat := ((39221850446428571501 : Rat) / 50000000000000000000)
def block169RightL : Rat := ((8921207589285714293 : Rat) / 5000000000000000000)
def block169RightR : Rat := ((139221850446428571501 : Rat) / 50000000000000000000)

def block169LeftBoxes : List RatBox := [
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3921207589285714293 : Rat) / 5000000000000000000), R := ((39221850446428571501 : Rat) / 50000000000000000000), D0 := ((39221850446428571501 : Rat) / 50000000000000000000), D1 := ((5166167910714285707 : Rat) / 5000000000000000000), D2 := ((8868467410714285707 : Rat) / 5000000000000000000), D3 := ((19367143589285714251 : Rat) / 10000000000000000000), D4 := ((10001245285714285207 : Rat) / 5000000000000000000), LB := ((21516987963594303 : Rat) / 10000000000000000000) }
]

def block169LeftCertificate : Bool :=
  allBoxesValid block169LeftBoxes &&
  coversFromBool block169LeftBoxes block169LeftL block169LeftR

theorem block169LeftCertificate_eq_true :
    block169LeftCertificate = true := by
  native_decide

def block169RightChunk000 : List RatBox := [
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8921207589285714293 : Rat) / 5000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((166167910714285707 : Rat) / 5000000000000000000), D2 := ((3868467410714285707 : Rat) / 5000000000000000000), D3 := ((9367143589285714251 : Rat) / 10000000000000000000), D4 := ((5001245285714285207 : Rat) / 5000000000000000000), LB := ((2817479955108387 : Rat) / 500000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((1316838591365691 : Rat) / 1250000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((18417549333926053 : Rat) / 50000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((15732932268284033 : Rat) / 100000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((9015252302548869 : Rat) / 100000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((1618585717476681 : Rat) / 500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((3159504092368537 : Rat) / 500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((9947120850595709 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((2694973744539253 : Rat) / 200000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((61086322624999968141 : Rat) / 320000000000000000000), LB := ((8783579455702323 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((2256856329524007 : Rat) / 500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((1727615821099579 : Rat) / 2500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((521716370182123 : Rat) / 125000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((26697860973226017 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((6489275928893007 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((6283500048046009 : Rat) / 100000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((5881907597723099 : Rat) / 2500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((9282850587229441 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((1747599521345379 : Rat) / 1250000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((4890317722934523 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((1194646682022571 : Rat) / 2000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((5133827783533329 : Rat) / 20000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((8179268473180873 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((1500481979013979 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((13756953309595477 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((6308058995693061 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((11583518091525247 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((1066038227745203 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((4923982146205347 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((1829508728545537 : Rat) / 2000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((1712085261857177 : Rat) / 2000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((8087945483976067 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((7731462332294659 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((468272923953017 : Rat) / 625000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((3686039173849409 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((737204696641347 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((7493753889108723 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((7738712585977359 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((8108469692926501 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((4302302996179591 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((4614368715408629 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((4991258087694711 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((10867631710596293 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((118858119776033 : Rat) / 100000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((6519412278942621 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((7164238951623131 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((63026490458441 : Rat) / 40000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((4331288192961219 : Rat) / 2500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((3188308129564027 : Rat) / 12500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((803766161919621 : Rat) / 1250000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((5451647884600619 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((1598742752213389 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((135629236598947 : Rat) / 62500000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((3393162040053571427101 : Rat) / 1280000000000000000000), D0 := ((3393162040053571427101 : Rat) / 1280000000000000000000), D1 := ((1066793912053571427101 : Rat) / 1280000000000000000000), D2 := ((119005240053571427101 : Rat) / 1280000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((2806213200901131 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3393162040053571427101 : Rat) / 1280000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 256000000000000000000), D4 := ((170985895946428444899 : Rat) / 1280000000000000000000), LB := ((17545936373960097 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((10190401644883107 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((348456950675681 : Rat) / 125000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((9720825803685773 : Rat) / 2000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((8011056304537967 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((3355488245376459 : Rat) / 500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((15337966079328469 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((430462313982142856881 : Rat) / 160000000000000000000), D0 := ((430462313982142856881 : Rat) / 160000000000000000000), D1 := ((139666297982142856881 : Rat) / 160000000000000000000), D2 := ((21192713982142856881 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((23025236742949817 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((430462313982142856881 : Rat) / 160000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 160000000000000000000), D4 := ((15056178017857127119 : Rat) / 160000000000000000000), LB := ((141332165159673 : Rat) / 2500000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((433435732808411 : Rat) / 5000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((68420653995535714257 : Rat) / 25000000000000000000), D0 := ((68420653995535714257 : Rat) / 25000000000000000000), D1 := ((22983776495535714257 : Rat) / 25000000000000000000), D2 := ((4472278995535714257 : Rat) / 25000000000000000000), D3 := ((793514151785714329 : Rat) / 50000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((11908376963626177 : Rat) / 100000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((68420653995535714257 : Rat) / 25000000000000000000), R := ((274476130133928571357 : Rat) / 100000000000000000000), D0 := ((274476130133928571357 : Rat) / 100000000000000000000), D1 := ((92728620133928571357 : Rat) / 100000000000000000000), D2 := ((18682630133928571357 : Rat) / 100000000000000000000), D3 := ((2380542455357142987 : Rat) / 100000000000000000000), D4 := ((1191610379464283243 : Rat) / 25000000000000000000), LB := ((3875113523717541 : Rat) / 62500000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((274476130133928571357 : Rat) / 100000000000000000000), R := ((137634822142857142843 : Rat) / 50000000000000000000), D0 := ((137634822142857142843 : Rat) / 50000000000000000000), D1 := ((46761067142857142843 : Rat) / 50000000000000000000), D2 := ((9738072142857142843 : Rat) / 50000000000000000000), D3 := ((793514151785714329 : Rat) / 25000000000000000000), D4 := ((3972927366071418643 : Rat) / 100000000000000000000), LB := ((701019662136057 : Rat) / 50000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((137634822142857142843 : Rat) / 50000000000000000000), R := ((551332802723214285701 : Rat) / 200000000000000000000), D0 := ((551332802723214285701 : Rat) / 200000000000000000000), D1 := ((187837782723214285701 : Rat) / 200000000000000000000), D2 := ((39745802723214285701 : Rat) / 200000000000000000000), D3 := ((7141627366071428961 : Rat) / 200000000000000000000), D4 := ((1589706607142852157 : Rat) / 50000000000000000000), LB := ((7833592043209991 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((551332802723214285701 : Rat) / 200000000000000000000), R := ((1103459119598214285731 : Rat) / 400000000000000000000), D0 := ((1103459119598214285731 : Rat) / 400000000000000000000), D1 := ((376469079598214285731 : Rat) / 400000000000000000000), D2 := ((80285119598214285731 : Rat) / 400000000000000000000), D3 := ((15076768883928572251 : Rat) / 400000000000000000000), D4 := ((5565312276785694299 : Rat) / 200000000000000000000), LB := ((389239867190741 : Rat) / 50000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1103459119598214285731 : Rat) / 400000000000000000000), R := ((55212631687500000003 : Rat) / 20000000000000000000), D0 := ((55212631687500000003 : Rat) / 20000000000000000000), D1 := ((18863129687500000003 : Rat) / 20000000000000000000), D2 := ((4053931687500000003 : Rat) / 20000000000000000000), D3 := ((793514151785714329 : Rat) / 20000000000000000000), D4 := ((10337110401785674269 : Rat) / 400000000000000000000), LB := ((434783068089839 : Rat) / 200000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((55212631687500000003 : Rat) / 20000000000000000000), R := ((2209298781651785714449 : Rat) / 800000000000000000000), D0 := ((2209298781651785714449 : Rat) / 800000000000000000000), D1 := ((755318701651785714449 : Rat) / 800000000000000000000), D2 := ((162950781651785714449 : Rat) / 800000000000000000000), D3 := ((32534080223214287489 : Rat) / 800000000000000000000), D4 := ((477179812499997997 : Rat) / 20000000000000000000), LB := ((19464683710740671 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2209298781651785714449 : Rat) / 800000000000000000000), R := ((1105046147901785714389 : Rat) / 400000000000000000000), D0 := ((1105046147901785714389 : Rat) / 400000000000000000000), D1 := ((378056107901785714389 : Rat) / 400000000000000000000), D2 := ((81872147901785714389 : Rat) / 400000000000000000000), D3 := ((16663797187500000909 : Rat) / 400000000000000000000), D4 := ((18293678348214205551 : Rat) / 800000000000000000000), LB := ((19090797751091237 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1105046147901785714389 : Rat) / 400000000000000000000), R := ((2210885809955357143107 : Rat) / 800000000000000000000), D0 := ((2210885809955357143107 : Rat) / 800000000000000000000), D1 := ((756905729955357143107 : Rat) / 800000000000000000000), D2 := ((164537809955357143107 : Rat) / 800000000000000000000), D3 := ((34121108526785716147 : Rat) / 800000000000000000000), D4 := ((8750082098214245611 : Rat) / 400000000000000000000), LB := ((4271714767076773 : Rat) / 20000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2210885809955357143107 : Rat) / 800000000000000000000), R := ((4422565134062500000543 : Rat) / 1600000000000000000000), D0 := ((4422565134062500000543 : Rat) / 1600000000000000000000), D1 := ((1514604974062500000543 : Rat) / 1600000000000000000000), D2 := ((329869134062500000543 : Rat) / 1600000000000000000000), D3 := ((69035731205357146623 : Rat) / 1600000000000000000000), D4 := ((16706650044642776893 : Rat) / 800000000000000000000), LB := ((18650399855326683 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4422565134062500000543 : Rat) / 1600000000000000000000), R := ((552919831026785714359 : Rat) / 200000000000000000000), D0 := ((552919831026785714359 : Rat) / 200000000000000000000), D1 := ((189424811026785714359 : Rat) / 200000000000000000000), D2 := ((41332831026785714359 : Rat) / 200000000000000000000), D3 := ((8728655669642857619 : Rat) / 200000000000000000000), D4 := ((32619785937499839457 : Rat) / 1600000000000000000000), LB := ((6321122372813237 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((552919831026785714359 : Rat) / 200000000000000000000), R := ((4424152162366071429201 : Rat) / 1600000000000000000000), D0 := ((4424152162366071429201 : Rat) / 1600000000000000000000), D1 := ((1516192002366071429201 : Rat) / 1600000000000000000000), D2 := ((331456162366071429201 : Rat) / 1600000000000000000000), D3 := ((70622759508928575281 : Rat) / 1600000000000000000000), D4 := ((3978283973214265641 : Rat) / 200000000000000000000), LB := ((7457039819142031 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4424152162366071429201 : Rat) / 1600000000000000000000), R := ((442494567651785714353 : Rat) / 160000000000000000000), D0 := ((442494567651785714353 : Rat) / 160000000000000000000), D1 := ((151698551651785714353 : Rat) / 160000000000000000000), D2 := ((33224967651785714353 : Rat) / 160000000000000000000), D3 := ((7141627366071428961 : Rat) / 160000000000000000000), D4 := ((31032757633928410799 : Rat) / 1600000000000000000000), LB := ((624069626137369 : Rat) / 2000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((442494567651785714353 : Rat) / 160000000000000000000), R := ((8850684867187500001389 : Rat) / 3200000000000000000000), D0 := ((8850684867187500001389 : Rat) / 3200000000000000000000), D1 := ((3034764547187500001389 : Rat) / 3200000000000000000000), D2 := ((665292867187500001389 : Rat) / 3200000000000000000000), D3 := ((143626061473214293549 : Rat) / 3200000000000000000000), D4 := ((3023924348214269647 : Rat) / 160000000000000000000), LB := ((363389996504343 : Rat) / 250000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8850684867187500001389 : Rat) / 3200000000000000000000), R := ((4425739190669642857859 : Rat) / 1600000000000000000000), D0 := ((4425739190669642857859 : Rat) / 1600000000000000000000), D1 := ((1517779030669642857859 : Rat) / 1600000000000000000000), D2 := ((333043190669642857859 : Rat) / 1600000000000000000000), D3 := ((72209787812500003939 : Rat) / 1600000000000000000000), D4 := ((59684972812499678611 : Rat) / 3200000000000000000000), LB := ((2618410140096783 : Rat) / 2000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4425739190669642857859 : Rat) / 1600000000000000000000), R := ((8852271895491071430047 : Rat) / 3200000000000000000000), D0 := ((8852271895491071430047 : Rat) / 3200000000000000000000), D1 := ((3036351575491071430047 : Rat) / 3200000000000000000000), D2 := ((666879895491071430047 : Rat) / 3200000000000000000000), D3 := ((145213089776785722207 : Rat) / 3200000000000000000000), D4 := ((29445729330356982141 : Rat) / 1600000000000000000000), LB := ((2969998690710851 : Rat) / 2500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8852271895491071430047 : Rat) / 3200000000000000000000), R := ((1106633176205357143047 : Rat) / 400000000000000000000), D0 := ((1106633176205357143047 : Rat) / 400000000000000000000), D1 := ((379643136205357143047 : Rat) / 400000000000000000000), D2 := ((83459176205357143047 : Rat) / 400000000000000000000), D3 := ((18250825491071429567 : Rat) / 400000000000000000000), D4 := ((58097944508928249953 : Rat) / 3200000000000000000000), LB := ((5451877175686459 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1106633176205357143047 : Rat) / 400000000000000000000), R := ((1770771784758928571741 : Rat) / 640000000000000000000), D0 := ((1770771784758928571741 : Rat) / 640000000000000000000), D1 := ((607587720758928571741 : Rat) / 640000000000000000000), D2 := ((133693384758928571741 : Rat) / 640000000000000000000), D3 := ((29360023616071430173 : Rat) / 640000000000000000000), D4 := ((7163053794642816953 : Rat) / 400000000000000000000), LB := ((5083930498936129 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1770771784758928571741 : Rat) / 640000000000000000000), R := ((4427326218973214286517 : Rat) / 1600000000000000000000), D0 := ((4427326218973214286517 : Rat) / 1600000000000000000000), D1 := ((1519366058973214286517 : Rat) / 1600000000000000000000), D2 := ((334630218973214286517 : Rat) / 1600000000000000000000), D3 := ((73796816116071432597 : Rat) / 1600000000000000000000), D4 := ((11302183241071364259 : Rat) / 640000000000000000000), LB := ((2419266580272611 : Rat) / 2500000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4427326218973214286517 : Rat) / 1600000000000000000000), R := ((8855445952098214287363 : Rat) / 3200000000000000000000), D0 := ((8855445952098214287363 : Rat) / 3200000000000000000000), D1 := ((3039525632098214287363 : Rat) / 3200000000000000000000), D2 := ((670053952098214287363 : Rat) / 3200000000000000000000), D3 := ((148387146383928579523 : Rat) / 3200000000000000000000), D4 := ((27858701026785553483 : Rat) / 1600000000000000000000), LB := ((1887270730597801 : Rat) / 2000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8855445952098214287363 : Rat) / 3200000000000000000000), R := ((2214059866562500000423 : Rat) / 800000000000000000000), D0 := ((2214059866562500000423 : Rat) / 800000000000000000000), D1 := ((760079786562500000423 : Rat) / 800000000000000000000), D2 := ((167711866562500000423 : Rat) / 800000000000000000000), D3 := ((37295165133928573463 : Rat) / 800000000000000000000), D4 := ((54923887901785392637 : Rat) / 3200000000000000000000), LB := ((1890190098869149 : Rat) / 2000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2214059866562500000423 : Rat) / 800000000000000000000), R := ((8857032980401785716021 : Rat) / 3200000000000000000000), D0 := ((8857032980401785716021 : Rat) / 3200000000000000000000), D1 := ((3041112660401785716021 : Rat) / 3200000000000000000000), D2 := ((671640980401785716021 : Rat) / 3200000000000000000000), D3 := ((149974174687500008181 : Rat) / 3200000000000000000000), D4 := ((13532593437499919577 : Rat) / 800000000000000000000), LB := ((4863170933816219 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8857032980401785716021 : Rat) / 3200000000000000000000), R := ((177156529891071428607 : Rat) / 64000000000000000000), D0 := ((177156529891071428607 : Rat) / 64000000000000000000), D1 := ((60838123491071428607 : Rat) / 64000000000000000000), D2 := ((13448689891071428607 : Rat) / 64000000000000000000), D3 := ((15076768883928572251 : Rat) / 320000000000000000000), D4 := ((53336859598213963979 : Rat) / 3200000000000000000000), LB := ((10268284641919423 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((177156529891071428607 : Rat) / 64000000000000000000), R := ((8858620008705357144679 : Rat) / 3200000000000000000000), D0 := ((8858620008705357144679 : Rat) / 3200000000000000000000), D1 := ((3042699688705357144679 : Rat) / 3200000000000000000000), D2 := ((673228008705357144679 : Rat) / 3200000000000000000000), D3 := ((151561202991071436839 : Rat) / 3200000000000000000000), D4 := ((1050866908928564993 : Rat) / 64000000000000000000), LB := ((69267643195179 : Rat) / 62500000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8858620008705357144679 : Rat) / 3200000000000000000000), R := ((34607084073660714293 : Rat) / 12500000000000000000), D0 := ((34607084073660714293 : Rat) / 12500000000000000000), D1 := ((11888645323660714293 : Rat) / 12500000000000000000), D2 := ((2632896573660714293 : Rat) / 12500000000000000000), D3 := ((2380542455357142987 : Rat) / 50000000000000000000), D4 := ((51749831294642535321 : Rat) / 3200000000000000000000), LB := ((2435260903168257 : Rat) / 2000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((34607084073660714293 : Rat) / 12500000000000000000), R := ((8860207037008928573337 : Rat) / 3200000000000000000000), D0 := ((8860207037008928573337 : Rat) / 3200000000000000000000), D1 := ((3044286717008928573337 : Rat) / 3200000000000000000000), D2 := ((674815037008928573337 : Rat) / 3200000000000000000000), D3 := ((153148231294642865497 : Rat) / 3200000000000000000000), D4 := ((199048113839284457 : Rat) / 12500000000000000000), LB := ((13555398805094043 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8860207037008928573337 : Rat) / 3200000000000000000000), R := ((4430500275580357143833 : Rat) / 1600000000000000000000), D0 := ((4430500275580357143833 : Rat) / 1600000000000000000000), D1 := ((1522540115580357143833 : Rat) / 1600000000000000000000), D2 := ((337804275580357143833 : Rat) / 1600000000000000000000), D3 := ((76970872723214289913 : Rat) / 1600000000000000000000), D4 := ((50162802991071106663 : Rat) / 3200000000000000000000), LB := ((15227115748999709 : Rat) / 10000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4430500275580357143833 : Rat) / 1600000000000000000000), R := ((2215646894866071429081 : Rat) / 800000000000000000000), D0 := ((2215646894866071429081 : Rat) / 800000000000000000000), D1 := ((761666814866071429081 : Rat) / 800000000000000000000), D2 := ((169298894866071429081 : Rat) / 800000000000000000000), D3 := ((38882193437500002121 : Rat) / 800000000000000000000), D4 := ((24684644419642696167 : Rat) / 1600000000000000000000), LB := ((1500452195539459 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2215646894866071429081 : Rat) / 800000000000000000000), R := ((4432087303883928572491 : Rat) / 1600000000000000000000), D0 := ((4432087303883928572491 : Rat) / 1600000000000000000000), D1 := ((1524127143883928572491 : Rat) / 1600000000000000000000), D2 := ((339391303883928572491 : Rat) / 1600000000000000000000), D3 := ((78557901026785718571 : Rat) / 1600000000000000000000), D4 := ((11945565133928490919 : Rat) / 800000000000000000000), LB := ((3982436156731439 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4432087303883928572491 : Rat) / 1600000000000000000000), R := ((221644040901785714341 : Rat) / 80000000000000000000), D0 := ((221644040901785714341 : Rat) / 80000000000000000000), D1 := ((76246032901785714341 : Rat) / 80000000000000000000), D2 := ((17009240901785714341 : Rat) / 80000000000000000000), D3 := ((793514151785714329 : Rat) / 16000000000000000000), D4 := ((23097616116071267509 : Rat) / 1600000000000000000000), LB := ((7112792474832097 : Rat) / 5000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((221644040901785714341 : Rat) / 80000000000000000000), R := ((4433674332187500001149 : Rat) / 1600000000000000000000), D0 := ((4433674332187500001149 : Rat) / 1600000000000000000000), D1 := ((1525714172187500001149 : Rat) / 1600000000000000000000), D2 := ((340978332187500001149 : Rat) / 1600000000000000000000), D3 := ((80144929330357147229 : Rat) / 1600000000000000000000), D4 := ((1115205098214277659 : Rat) / 80000000000000000000), LB := ((2185756911057213 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4433674332187500001149 : Rat) / 1600000000000000000000), R := ((2217233923169642857739 : Rat) / 800000000000000000000), D0 := ((2217233923169642857739 : Rat) / 800000000000000000000), D1 := ((763253843169642857739 : Rat) / 800000000000000000000), D2 := ((170885923169642857739 : Rat) / 800000000000000000000), D3 := ((40469221741071430779 : Rat) / 800000000000000000000), D4 := ((21510587812499838851 : Rat) / 1600000000000000000000), LB := ((618875041844813 : Rat) / 200000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2217233923169642857739 : Rat) / 800000000000000000000), R := ((554506859330357143017 : Rat) / 200000000000000000000), D0 := ((554506859330357143017 : Rat) / 200000000000000000000), D1 := ((191011839330357143017 : Rat) / 200000000000000000000), D2 := ((42919859330357143017 : Rat) / 200000000000000000000), D3 := ((10315683973214286277 : Rat) / 200000000000000000000), D4 := ((10358536830357062261 : Rat) / 800000000000000000000), LB := ((1416008458787421 : Rat) / 1000000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((554506859330357143017 : Rat) / 200000000000000000000), R := ((2218820951473214286397 : Rat) / 800000000000000000000), D0 := ((2218820951473214286397 : Rat) / 800000000000000000000), D1 := ((764840871473214286397 : Rat) / 800000000000000000000), D2 := ((172472951473214286397 : Rat) / 800000000000000000000), D3 := ((42056250044642859437 : Rat) / 800000000000000000000), D4 := ((2391255669642836983 : Rat) / 200000000000000000000), LB := ((255055878616451 : Rat) / 62500000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2218820951473214286397 : Rat) / 800000000000000000000), R := ((1109807232812500000363 : Rat) / 400000000000000000000), D0 := ((1109807232812500000363 : Rat) / 400000000000000000000), D1 := ((382817192812500000363 : Rat) / 400000000000000000000), D2 := ((86633232812500000363 : Rat) / 400000000000000000000), D3 := ((21424882098214286883 : Rat) / 400000000000000000000), D4 := ((8771508526785633603 : Rat) / 800000000000000000000), LB := ((1876281895009213 : Rat) / 250000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1109807232812500000363 : Rat) / 400000000000000000000), R := ((277650186741071428673 : Rat) / 100000000000000000000), D0 := ((277650186741071428673 : Rat) / 100000000000000000000), D1 := ((95902676741071428673 : Rat) / 100000000000000000000), D2 := ((21856686741071428673 : Rat) / 100000000000000000000), D3 := ((5554599062500000303 : Rat) / 100000000000000000000), D4 := ((3988997187499959637 : Rat) / 400000000000000000000), LB := ((524626978162539 : Rat) / 80000000000000000) }
]

def block169RightChunk000L : Rat := ((8921207589285714293 : Rat) / 5000000000000000000)
def block169RightChunk000R : Rat := ((277650186741071428673 : Rat) / 100000000000000000000)

def block169RightChunk000Certificate : Bool :=
  allBoxesValid block169RightChunk000 &&
  coversFromBool block169RightChunk000 block169RightChunk000L block169RightChunk000R

theorem block169RightChunk000Certificate_eq_true :
    block169RightChunk000Certificate = true := by
  native_decide

def block169RightChunk001 : List RatBox := [
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((277650186741071428673 : Rat) / 100000000000000000000), R := ((22243755505357142867 : Rat) / 8000000000000000000), D0 := ((22243755505357142867 : Rat) / 8000000000000000000), D1 := ((7703954705357142867 : Rat) / 8000000000000000000), D2 := ((1780275505357142867 : Rat) / 8000000000000000000), D3 := ((2380542455357142987 : Rat) / 40000000000000000000), D4 := ((798870758928561327 : Rat) / 100000000000000000000), LB := ((2127206294000969 : Rat) / 250000000000000000) },
  { w1 := ((4569007558247531 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((16699298570650783 : Rat) / 100000000000000000), w4 := ((10170006993501911 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((22243755505357142867 : Rat) / 8000000000000000000), R := ((139221850446428571501 : Rat) / 50000000000000000000), D0 := ((139221850446428571501 : Rat) / 50000000000000000000), D1 := ((48348095446428571501 : Rat) / 50000000000000000000), D2 := ((11325100446428571501 : Rat) / 50000000000000000000), D3 := ((793514151785714329 : Rat) / 12500000000000000000), D4 := ((32169094642856333 : Rat) / 8000000000000000000), LB := ((13977386567730149 : Rat) / 250000000000000000) }
]

def block169RightChunk001L : Rat := ((277650186741071428673 : Rat) / 100000000000000000000)
def block169RightChunk001R : Rat := ((139221850446428571501 : Rat) / 50000000000000000000)

def block169RightChunk001Certificate : Bool :=
  allBoxesValid block169RightChunk001 &&
  coversFromBool block169RightChunk001 block169RightChunk001L block169RightChunk001R

theorem block169RightChunk001Certificate_eq_true :
    block169RightChunk001Certificate = true := by
  native_decide

def block169RightChainCertificate : Bool :=
  decide (
    block169RightL = ((8921207589285714293 : Rat) / 5000000000000000000) /\
    ((277650186741071428673 : Rat) / 100000000000000000000) = ((277650186741071428673 : Rat) / 100000000000000000000) /\
    ((139221850446428571501 : Rat) / 50000000000000000000) = block169RightR)

theorem block169RightChainCertificate_eq_true :
    block169RightChainCertificate = true := by
  native_decide

def block169LeftBoxCount : Nat := boxCount block169LeftBoxes
def block169RightBoxCount : Nat := 102

def block169_rational_certificate : Prop :=
    block169LeftCertificate = true /\
    block169RightChainCertificate = true /\
    block169RightChunk000Certificate = true /\
    block169RightChunk001Certificate = true

theorem block169_rational_certificate_proof :
    block169_rational_certificate := by
  exact ⟨block169LeftCertificate_eq_true, block169RightChainCertificate_eq_true, block169RightChunk000Certificate_eq_true, block169RightChunk001Certificate_eq_true⟩

end Block169
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block169

open Set

def block169W1 : Rat := ((4569007558247531 : Rat) / 2500000000000000)
def block169W2 : Rat := (0 : Rat)
def block169W3 : Rat := ((16699298570650783 : Rat) / 100000000000000000)
def block169W4 : Rat := ((10170006993501911 : Rat) / 100000000000000000)
def block169S1 : Rat := ((18174751 : Rat) / 10000000)
def block169S2 : Rat := ((511587 : Rat) / 200000)
def block169S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block169S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block169V (y : ℝ) : ℝ :=
  ratPotential block169W1 block169W2 block169W3 block169W4 block169S1 block169S2 block169S3 block169S4 y

def block169LeftParamsCertificate : Bool :=
  allBoxesSameParams block169LeftBoxes block169W1 block169W2 block169W3 block169W4 block169S1 block169S2 block169S3 block169S4

theorem block169LeftParamsCertificate_eq_true :
    block169LeftParamsCertificate = true := by
  native_decide

theorem block169_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block169LeftL : ℝ) (block169LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block169S1 : ℝ))
    (hy2ne : y ≠ (block169S2 : ℝ))
    (hy3ne : y ≠ (block169S3 : ℝ))
    (hy4ne : y ≠ (block169S4 : ℝ)) :
    0 < block169V y := by
  have hcert := block169LeftCertificate_eq_true
  unfold block169LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block169LeftBoxes) (lo := block169LeftL) (hi := block169LeftR)
    (w1 := block169W1) (w2 := block169W2) (w3 := block169W3) (w4 := block169W4)
    (s1 := block169S1) (s2 := block169S2) (s3 := block169S3) (s4 := block169S4)
    hboxes hcover block169LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block169RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block169RightChunk000 block169W1 block169W2 block169W3 block169W4 block169S1 block169S2 block169S3 block169S4

theorem block169RightChunk000ParamsCertificate_eq_true :
    block169RightChunk000ParamsCertificate = true := by
  native_decide

theorem block169_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block169RightChunk000L : ℝ) (block169RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block169S1 : ℝ))
    (hy2ne : y ≠ (block169S2 : ℝ))
    (hy3ne : y ≠ (block169S3 : ℝ))
    (hy4ne : y ≠ (block169S4 : ℝ)) :
    0 < block169V y := by
  have hcert := block169RightChunk000Certificate_eq_true
  unfold block169RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block169RightChunk000) (lo := block169RightChunk000L) (hi := block169RightChunk000R)
    (w1 := block169W1) (w2 := block169W2) (w3 := block169W3) (w4 := block169W4)
    (s1 := block169S1) (s2 := block169S2) (s3 := block169S3) (s4 := block169S4)
    hboxes hcover block169RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block169RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block169RightChunk001 block169W1 block169W2 block169W3 block169W4 block169S1 block169S2 block169S3 block169S4

theorem block169RightChunk001ParamsCertificate_eq_true :
    block169RightChunk001ParamsCertificate = true := by
  native_decide

theorem block169_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block169RightChunk001L : ℝ) (block169RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block169S1 : ℝ))
    (hy2ne : y ≠ (block169S2 : ℝ))
    (hy3ne : y ≠ (block169S3 : ℝ))
    (hy4ne : y ≠ (block169S4 : ℝ)) :
    0 < block169V y := by
  have hcert := block169RightChunk001Certificate_eq_true
  unfold block169RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block169RightChunk001) (lo := block169RightChunk001L) (hi := block169RightChunk001R)
    (w1 := block169W1) (w2 := block169W2) (w3 := block169W3) (w4 := block169W4)
    (s1 := block169S1) (s2 := block169S2) (s3 := block169S3) (s4 := block169S4)
    hboxes hcover block169RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block169_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block169RightL : ℝ) (block169RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block169S1 : ℝ))
    (hy2ne : y ≠ (block169S2 : ℝ))
    (hy3ne : y ≠ (block169S3 : ℝ))
    (hy4ne : y ≠ (block169S4 : ℝ)) :
    0 < block169V y := by
  by_cases h0 : y ≤ (block169RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block169RightChunk000L : ℝ) (block169RightChunk000R : ℝ) := by
      have hL : (block169RightChunk000L : ℝ) = (block169RightL : ℝ) := by
        norm_num [block169RightChunk000L, block169RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block169_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block169RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block169RightChunk001L : ℝ) = (block169RightChunk000R : ℝ) := by
      norm_num [block169RightChunk001L, block169RightChunk000R]
    have hR : (block169RightChunk001R : ℝ) = (block169RightR : ℝ) := by
      norm_num [block169RightChunk001R, block169RightR]
    have hyc : y ∈ Icc (block169RightChunk001L : ℝ) (block169RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block169_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block169_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block169LeftL : ℝ) (block169LeftR : ℝ) →
    y ≠ 0 → y ≠ (block169S1 : ℝ) → y ≠ (block169S2 : ℝ) →
    y ≠ (block169S3 : ℝ) → y ≠ (block169S4 : ℝ) → 0 < block169V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block169RightL : ℝ) (block169RightR : ℝ) →
    y ≠ 0 → y ≠ (block169S1 : ℝ) → y ≠ (block169S2 : ℝ) →
    y ≠ (block169S3 : ℝ) → y ≠ (block169S4 : ℝ) → 0 < block169V y)

theorem block169_reallog_certificate_proof :
    block169_reallog_certificate := by
  exact ⟨block169_left_V_pos, block169_right_V_pos⟩

end Block169
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block169.block169V
#check Erdos1038Lean.M1817475.Block169.block169_left_V_pos
#check Erdos1038Lean.M1817475.Block169.block169_right_V_pos
#check Erdos1038Lean.M1817475.Block169.block169_reallog_certificate_proof
