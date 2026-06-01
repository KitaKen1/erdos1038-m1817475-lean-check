import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block413

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block413

open Set

def block413W1 : Rat := ((7088633491208467 : Rat) / 10000000000000000)
def block413W2 : Rat := (0 : Rat)
def block413W3 : Rat := ((2892599521801751 : Rat) / 10000000000000000)
def block413W4 : Rat := ((1104171517950471 : Rat) / 12500000000000000)
def block413S1 : Rat := ((18174751 : Rat) / 10000000)
def block413S2 : Rat := ((511587 : Rat) / 200000)
def block413S3 : Rat := ((132059775982142857217 : Rat) / 50000000000000000000)
def block413S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block413V (y : ℝ) : ℝ :=
  ratPotential block413W1 block413W2 block413W3 block413W4 block413S1 block413S2 block413S3 block413S4 y

def block413LeftParamsCertificate : Bool :=
  allBoxesSameParams block413LeftBoxes block413W1 block413W2 block413W3 block413W4 block413S1 block413S2 block413S3 block413S4

theorem block413LeftParamsCertificate_eq_true :
    block413LeftParamsCertificate = true := by
  native_decide

theorem block413_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block413LeftL : ℝ) (block413LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block413S1 : ℝ))
    (hy2ne : y ≠ (block413S2 : ℝ))
    (hy3ne : y ≠ (block413S3 : ℝ))
    (hy4ne : y ≠ (block413S4 : ℝ)) :
    0 < block413V y := by
  have hcert := block413LeftCertificate_eq_true
  unfold block413LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block413LeftBoxes) (lo := block413LeftL) (hi := block413LeftR)
    (w1 := block413W1) (w2 := block413W2) (w3 := block413W3) (w4 := block413W4)
    (s1 := block413S1) (s2 := block413S2) (s3 := block413S3) (s4 := block413S4)
    hboxes hcover block413LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block413RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block413RightChunk000 block413W1 block413W2 block413W3 block413W4 block413S1 block413S2 block413S3 block413S4

theorem block413RightChunk000ParamsCertificate_eq_true :
    block413RightChunk000ParamsCertificate = true := by
  native_decide

theorem block413_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block413RightChunk000L : ℝ) (block413RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block413S1 : ℝ))
    (hy2ne : y ≠ (block413S2 : ℝ))
    (hy3ne : y ≠ (block413S3 : ℝ))
    (hy4ne : y ≠ (block413S4 : ℝ)) :
    0 < block413V y := by
  have hcert := block413RightChunk000Certificate_eq_true
  unfold block413RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block413RightChunk000) (lo := block413RightChunk000L) (hi := block413RightChunk000R)
    (w1 := block413W1) (w2 := block413W2) (w3 := block413W3) (w4 := block413W4)
    (s1 := block413S1) (s2 := block413S2) (s3 := block413S3) (s4 := block413S4)
    hboxes hcover block413RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block413RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block413RightChunk001 block413W1 block413W2 block413W3 block413W4 block413S1 block413S2 block413S3 block413S4

theorem block413RightChunk001ParamsCertificate_eq_true :
    block413RightChunk001ParamsCertificate = true := by
  native_decide

theorem block413_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block413RightChunk001L : ℝ) (block413RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block413S1 : ℝ))
    (hy2ne : y ≠ (block413S2 : ℝ))
    (hy3ne : y ≠ (block413S3 : ℝ))
    (hy4ne : y ≠ (block413S4 : ℝ)) :
    0 < block413V y := by
  have hcert := block413RightChunk001Certificate_eq_true
  unfold block413RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block413RightChunk001) (lo := block413RightChunk001L) (hi := block413RightChunk001R)
    (w1 := block413W1) (w2 := block413W2) (w3 := block413W3) (w4 := block413W4)
    (s1 := block413S1) (s2 := block413S2) (s3 := block413S3) (s4 := block413S4)
    hboxes hcover block413RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block413_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block413RightL : ℝ) (block413RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block413S1 : ℝ))
    (hy2ne : y ≠ (block413S2 : ℝ))
    (hy3ne : y ≠ (block413S3 : ℝ))
    (hy4ne : y ≠ (block413S4 : ℝ)) :
    0 < block413V y := by
  by_cases h0 : y ≤ (block413RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block413RightChunk000L : ℝ) (block413RightChunk000R : ℝ) := by
      have hL : (block413RightChunk000L : ℝ) = (block413RightL : ℝ) := by
        norm_num [block413RightChunk000L, block413RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block413_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block413RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block413RightChunk001L : ℝ) = (block413RightChunk000R : ℝ) := by
      norm_num [block413RightChunk001L, block413RightChunk000R]
    have hR : (block413RightChunk001R : ℝ) = (block413RightR : ℝ) := by
      norm_num [block413RightChunk001R, block413RightR]
    have hyc : y ∈ Icc (block413RightChunk001L : ℝ) (block413RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block413_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block413_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block413LeftL : ℝ) (block413LeftR : ℝ) →
    y ≠ 0 → y ≠ (block413S1 : ℝ) → y ≠ (block413S2 : ℝ) →
    y ≠ (block413S3 : ℝ) → y ≠ (block413S4 : ℝ) → 0 < block413V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block413RightL : ℝ) (block413RightR : ℝ) →
    y ≠ 0 → y ≠ (block413S1 : ℝ) → y ≠ (block413S2 : ℝ) →
    y ≠ (block413S3 : ℝ) → y ≠ (block413S4 : ℝ) → 0 < block413V y)

theorem block413_reallog_certificate_proof :
    block413_reallog_certificate := by
  exact ⟨block413_left_V_pos, block413_right_V_pos⟩

end Block413
end M1817475
end Erdos1038Lean
