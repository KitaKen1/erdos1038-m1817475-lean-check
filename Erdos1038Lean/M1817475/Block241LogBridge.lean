import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block241

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block241

open Set

def block241W1 : Rat := ((2151006998785813 : Rat) / 2500000000000000)
def block241W2 : Rat := ((8398728384418579 : Rat) / 100000000000000000)
def block241W3 : Rat := ((904203222056289 : Rat) / 25000000000000000)
def block241W4 : Rat := ((2166187217863933 : Rat) / 10000000000000000)
def block241S1 : Rat := ((18174751 : Rat) / 10000000)
def block241S2 : Rat := ((511587 : Rat) / 200000)
def block241S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block241S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block241V (y : ℝ) : ℝ :=
  ratPotential block241W1 block241W2 block241W3 block241W4 block241S1 block241S2 block241S3 block241S4 y

def block241LeftParamsCertificate : Bool :=
  allBoxesSameParams block241LeftBoxes block241W1 block241W2 block241W3 block241W4 block241S1 block241S2 block241S3 block241S4

theorem block241LeftParamsCertificate_eq_true :
    block241LeftParamsCertificate = true := by
  native_decide

theorem block241_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block241LeftL : ℝ) (block241LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block241S1 : ℝ))
    (hy2ne : y ≠ (block241S2 : ℝ))
    (hy3ne : y ≠ (block241S3 : ℝ))
    (hy4ne : y ≠ (block241S4 : ℝ)) :
    0 < block241V y := by
  have hcert := block241LeftCertificate_eq_true
  unfold block241LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block241LeftBoxes) (lo := block241LeftL) (hi := block241LeftR)
    (w1 := block241W1) (w2 := block241W2) (w3 := block241W3) (w4 := block241W4)
    (s1 := block241S1) (s2 := block241S2) (s3 := block241S3) (s4 := block241S4)
    hboxes hcover block241LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block241RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block241RightChunk000 block241W1 block241W2 block241W3 block241W4 block241S1 block241S2 block241S3 block241S4

theorem block241RightChunk000ParamsCertificate_eq_true :
    block241RightChunk000ParamsCertificate = true := by
  native_decide

theorem block241_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block241RightChunk000L : ℝ) (block241RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block241S1 : ℝ))
    (hy2ne : y ≠ (block241S2 : ℝ))
    (hy3ne : y ≠ (block241S3 : ℝ))
    (hy4ne : y ≠ (block241S4 : ℝ)) :
    0 < block241V y := by
  have hcert := block241RightChunk000Certificate_eq_true
  unfold block241RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block241RightChunk000) (lo := block241RightChunk000L) (hi := block241RightChunk000R)
    (w1 := block241W1) (w2 := block241W2) (w3 := block241W3) (w4 := block241W4)
    (s1 := block241S1) (s2 := block241S2) (s3 := block241S3) (s4 := block241S4)
    hboxes hcover block241RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block241RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block241RightChunk001 block241W1 block241W2 block241W3 block241W4 block241S1 block241S2 block241S3 block241S4

theorem block241RightChunk001ParamsCertificate_eq_true :
    block241RightChunk001ParamsCertificate = true := by
  native_decide

theorem block241_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block241RightChunk001L : ℝ) (block241RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block241S1 : ℝ))
    (hy2ne : y ≠ (block241S2 : ℝ))
    (hy3ne : y ≠ (block241S3 : ℝ))
    (hy4ne : y ≠ (block241S4 : ℝ)) :
    0 < block241V y := by
  have hcert := block241RightChunk001Certificate_eq_true
  unfold block241RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block241RightChunk001) (lo := block241RightChunk001L) (hi := block241RightChunk001R)
    (w1 := block241W1) (w2 := block241W2) (w3 := block241W3) (w4 := block241W4)
    (s1 := block241S1) (s2 := block241S2) (s3 := block241S3) (s4 := block241S4)
    hboxes hcover block241RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block241_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block241RightL : ℝ) (block241RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block241S1 : ℝ))
    (hy2ne : y ≠ (block241S2 : ℝ))
    (hy3ne : y ≠ (block241S3 : ℝ))
    (hy4ne : y ≠ (block241S4 : ℝ)) :
    0 < block241V y := by
  by_cases h0 : y ≤ (block241RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block241RightChunk000L : ℝ) (block241RightChunk000R : ℝ) := by
      have hL : (block241RightChunk000L : ℝ) = (block241RightL : ℝ) := by
        norm_num [block241RightChunk000L, block241RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block241_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block241RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block241RightChunk001L : ℝ) = (block241RightChunk000R : ℝ) := by
      norm_num [block241RightChunk001L, block241RightChunk000R]
    have hR : (block241RightChunk001R : ℝ) = (block241RightR : ℝ) := by
      norm_num [block241RightChunk001R, block241RightR]
    have hyc : y ∈ Icc (block241RightChunk001L : ℝ) (block241RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block241_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block241_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block241LeftL : ℝ) (block241LeftR : ℝ) →
    y ≠ 0 → y ≠ (block241S1 : ℝ) → y ≠ (block241S2 : ℝ) →
    y ≠ (block241S3 : ℝ) → y ≠ (block241S4 : ℝ) → 0 < block241V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block241RightL : ℝ) (block241RightR : ℝ) →
    y ≠ 0 → y ≠ (block241S1 : ℝ) → y ≠ (block241S2 : ℝ) →
    y ≠ (block241S3 : ℝ) → y ≠ (block241S4 : ℝ) → 0 < block241V y)

theorem block241_reallog_certificate_proof :
    block241_reallog_certificate := by
  exact ⟨block241_left_V_pos, block241_right_V_pos⟩

end Block241
end M1817475
end Erdos1038Lean
