import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block256

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block256

open Set

def block256W1 : Rat := ((221825396526037 : Rat) / 250000000000000)
def block256W2 : Rat := ((7660902443044137 : Rat) / 100000000000000000)
def block256W3 : Rat := ((19335491596598803 : Rat) / 100000000000000000)
def block256W4 : Rat := ((6422379506904037 : Rat) / 100000000000000000)
def block256S1 : Rat := ((18174751 : Rat) / 10000000)
def block256S2 : Rat := ((511587 : Rat) / 200000)
def block256S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block256S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block256V (y : ℝ) : ℝ :=
  ratPotential block256W1 block256W2 block256W3 block256W4 block256S1 block256S2 block256S3 block256S4 y

def block256LeftParamsCertificate : Bool :=
  allBoxesSameParams block256LeftBoxes block256W1 block256W2 block256W3 block256W4 block256S1 block256S2 block256S3 block256S4

theorem block256LeftParamsCertificate_eq_true :
    block256LeftParamsCertificate = true := by
  native_decide

theorem block256_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block256LeftL : ℝ) (block256LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block256S1 : ℝ))
    (hy2ne : y ≠ (block256S2 : ℝ))
    (hy3ne : y ≠ (block256S3 : ℝ))
    (hy4ne : y ≠ (block256S4 : ℝ)) :
    0 < block256V y := by
  have hcert := block256LeftCertificate_eq_true
  unfold block256LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block256LeftBoxes) (lo := block256LeftL) (hi := block256LeftR)
    (w1 := block256W1) (w2 := block256W2) (w3 := block256W3) (w4 := block256W4)
    (s1 := block256S1) (s2 := block256S2) (s3 := block256S3) (s4 := block256S4)
    hboxes hcover block256LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block256RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block256RightChunk000 block256W1 block256W2 block256W3 block256W4 block256S1 block256S2 block256S3 block256S4

theorem block256RightChunk000ParamsCertificate_eq_true :
    block256RightChunk000ParamsCertificate = true := by
  native_decide

theorem block256_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block256RightChunk000L : ℝ) (block256RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block256S1 : ℝ))
    (hy2ne : y ≠ (block256S2 : ℝ))
    (hy3ne : y ≠ (block256S3 : ℝ))
    (hy4ne : y ≠ (block256S4 : ℝ)) :
    0 < block256V y := by
  have hcert := block256RightChunk000Certificate_eq_true
  unfold block256RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block256RightChunk000) (lo := block256RightChunk000L) (hi := block256RightChunk000R)
    (w1 := block256W1) (w2 := block256W2) (w3 := block256W3) (w4 := block256W4)
    (s1 := block256S1) (s2 := block256S2) (s3 := block256S3) (s4 := block256S4)
    hboxes hcover block256RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block256RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block256RightChunk001 block256W1 block256W2 block256W3 block256W4 block256S1 block256S2 block256S3 block256S4

theorem block256RightChunk001ParamsCertificate_eq_true :
    block256RightChunk001ParamsCertificate = true := by
  native_decide

theorem block256_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block256RightChunk001L : ℝ) (block256RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block256S1 : ℝ))
    (hy2ne : y ≠ (block256S2 : ℝ))
    (hy3ne : y ≠ (block256S3 : ℝ))
    (hy4ne : y ≠ (block256S4 : ℝ)) :
    0 < block256V y := by
  have hcert := block256RightChunk001Certificate_eq_true
  unfold block256RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block256RightChunk001) (lo := block256RightChunk001L) (hi := block256RightChunk001R)
    (w1 := block256W1) (w2 := block256W2) (w3 := block256W3) (w4 := block256W4)
    (s1 := block256S1) (s2 := block256S2) (s3 := block256S3) (s4 := block256S4)
    hboxes hcover block256RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block256_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block256RightL : ℝ) (block256RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block256S1 : ℝ))
    (hy2ne : y ≠ (block256S2 : ℝ))
    (hy3ne : y ≠ (block256S3 : ℝ))
    (hy4ne : y ≠ (block256S4 : ℝ)) :
    0 < block256V y := by
  by_cases h0 : y ≤ (block256RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block256RightChunk000L : ℝ) (block256RightChunk000R : ℝ) := by
      have hL : (block256RightChunk000L : ℝ) = (block256RightL : ℝ) := by
        norm_num [block256RightChunk000L, block256RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block256_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block256RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block256RightChunk001L : ℝ) = (block256RightChunk000R : ℝ) := by
      norm_num [block256RightChunk001L, block256RightChunk000R]
    have hR : (block256RightChunk001R : ℝ) = (block256RightR : ℝ) := by
      norm_num [block256RightChunk001R, block256RightR]
    have hyc : y ∈ Icc (block256RightChunk001L : ℝ) (block256RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block256_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block256_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block256LeftL : ℝ) (block256LeftR : ℝ) →
    y ≠ 0 → y ≠ (block256S1 : ℝ) → y ≠ (block256S2 : ℝ) →
    y ≠ (block256S3 : ℝ) → y ≠ (block256S4 : ℝ) → 0 < block256V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block256RightL : ℝ) (block256RightR : ℝ) →
    y ≠ 0 → y ≠ (block256S1 : ℝ) → y ≠ (block256S2 : ℝ) →
    y ≠ (block256S3 : ℝ) → y ≠ (block256S4 : ℝ) → 0 < block256V y)

theorem block256_reallog_certificate_proof :
    block256_reallog_certificate := by
  exact ⟨block256_left_V_pos, block256_right_V_pos⟩

end Block256
end M1817475
end Erdos1038Lean
