import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block243

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block243

open Set

def block243W1 : Rat := ((1073103488715727 : Rat) / 1250000000000000)
def block243W2 : Rat := ((850178012373109 : Rat) / 10000000000000000)
def block243W3 : Rat := ((3883612205693427 : Rat) / 100000000000000000)
def block243W4 : Rat := ((2129025260902867 : Rat) / 10000000000000000)
def block243S1 : Rat := ((18174751 : Rat) / 10000000)
def block243S2 : Rat := ((511587 : Rat) / 200000)
def block243S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block243S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block243V (y : ℝ) : ℝ :=
  ratPotential block243W1 block243W2 block243W3 block243W4 block243S1 block243S2 block243S3 block243S4 y

def block243LeftParamsCertificate : Bool :=
  allBoxesSameParams block243LeftBoxes block243W1 block243W2 block243W3 block243W4 block243S1 block243S2 block243S3 block243S4

theorem block243LeftParamsCertificate_eq_true :
    block243LeftParamsCertificate = true := by
  native_decide

theorem block243_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block243LeftL : ℝ) (block243LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block243S1 : ℝ))
    (hy2ne : y ≠ (block243S2 : ℝ))
    (hy3ne : y ≠ (block243S3 : ℝ))
    (hy4ne : y ≠ (block243S4 : ℝ)) :
    0 < block243V y := by
  have hcert := block243LeftCertificate_eq_true
  unfold block243LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block243LeftBoxes) (lo := block243LeftL) (hi := block243LeftR)
    (w1 := block243W1) (w2 := block243W2) (w3 := block243W3) (w4 := block243W4)
    (s1 := block243S1) (s2 := block243S2) (s3 := block243S3) (s4 := block243S4)
    hboxes hcover block243LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block243RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block243RightChunk000 block243W1 block243W2 block243W3 block243W4 block243S1 block243S2 block243S3 block243S4

theorem block243RightChunk000ParamsCertificate_eq_true :
    block243RightChunk000ParamsCertificate = true := by
  native_decide

theorem block243_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block243RightChunk000L : ℝ) (block243RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block243S1 : ℝ))
    (hy2ne : y ≠ (block243S2 : ℝ))
    (hy3ne : y ≠ (block243S3 : ℝ))
    (hy4ne : y ≠ (block243S4 : ℝ)) :
    0 < block243V y := by
  have hcert := block243RightChunk000Certificate_eq_true
  unfold block243RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block243RightChunk000) (lo := block243RightChunk000L) (hi := block243RightChunk000R)
    (w1 := block243W1) (w2 := block243W2) (w3 := block243W3) (w4 := block243W4)
    (s1 := block243S1) (s2 := block243S2) (s3 := block243S3) (s4 := block243S4)
    hboxes hcover block243RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block243RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block243RightChunk001 block243W1 block243W2 block243W3 block243W4 block243S1 block243S2 block243S3 block243S4

theorem block243RightChunk001ParamsCertificate_eq_true :
    block243RightChunk001ParamsCertificate = true := by
  native_decide

theorem block243_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block243RightChunk001L : ℝ) (block243RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block243S1 : ℝ))
    (hy2ne : y ≠ (block243S2 : ℝ))
    (hy3ne : y ≠ (block243S3 : ℝ))
    (hy4ne : y ≠ (block243S4 : ℝ)) :
    0 < block243V y := by
  have hcert := block243RightChunk001Certificate_eq_true
  unfold block243RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block243RightChunk001) (lo := block243RightChunk001L) (hi := block243RightChunk001R)
    (w1 := block243W1) (w2 := block243W2) (w3 := block243W3) (w4 := block243W4)
    (s1 := block243S1) (s2 := block243S2) (s3 := block243S3) (s4 := block243S4)
    hboxes hcover block243RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block243_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block243RightL : ℝ) (block243RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block243S1 : ℝ))
    (hy2ne : y ≠ (block243S2 : ℝ))
    (hy3ne : y ≠ (block243S3 : ℝ))
    (hy4ne : y ≠ (block243S4 : ℝ)) :
    0 < block243V y := by
  by_cases h0 : y ≤ (block243RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block243RightChunk000L : ℝ) (block243RightChunk000R : ℝ) := by
      have hL : (block243RightChunk000L : ℝ) = (block243RightL : ℝ) := by
        norm_num [block243RightChunk000L, block243RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block243_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block243RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block243RightChunk001L : ℝ) = (block243RightChunk000R : ℝ) := by
      norm_num [block243RightChunk001L, block243RightChunk000R]
    have hR : (block243RightChunk001R : ℝ) = (block243RightR : ℝ) := by
      norm_num [block243RightChunk001R, block243RightR]
    have hyc : y ∈ Icc (block243RightChunk001L : ℝ) (block243RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block243_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block243_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block243LeftL : ℝ) (block243LeftR : ℝ) →
    y ≠ 0 → y ≠ (block243S1 : ℝ) → y ≠ (block243S2 : ℝ) →
    y ≠ (block243S3 : ℝ) → y ≠ (block243S4 : ℝ) → 0 < block243V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block243RightL : ℝ) (block243RightR : ℝ) →
    y ≠ 0 → y ≠ (block243S1 : ℝ) → y ≠ (block243S2 : ℝ) →
    y ≠ (block243S3 : ℝ) → y ≠ (block243S4 : ℝ) → 0 < block243V y)

theorem block243_reallog_certificate_proof :
    block243_reallog_certificate := by
  exact ⟨block243_left_V_pos, block243_right_V_pos⟩

end Block243
end M1817475
end Erdos1038Lean
