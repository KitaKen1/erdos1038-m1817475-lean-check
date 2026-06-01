import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block240

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block240

open Set

def block240W1 : Rat := ((4303341955056173 : Rat) / 5000000000000000)
def block240W2 : Rat := ((8371569579727087 : Rat) / 100000000000000000)
def block240W3 : Rat := ((17130433459541447 : Rat) / 500000000000000000)
def block240W4 : Rat := ((10944094503469147 : Rat) / 50000000000000000)
def block240S1 : Rat := ((18174751 : Rat) / 10000000)
def block240S2 : Rat := ((511587 : Rat) / 200000)
def block240S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block240S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block240V (y : ℝ) : ℝ :=
  ratPotential block240W1 block240W2 block240W3 block240W4 block240S1 block240S2 block240S3 block240S4 y

def block240LeftParamsCertificate : Bool :=
  allBoxesSameParams block240LeftBoxes block240W1 block240W2 block240W3 block240W4 block240S1 block240S2 block240S3 block240S4

theorem block240LeftParamsCertificate_eq_true :
    block240LeftParamsCertificate = true := by
  native_decide

theorem block240_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block240LeftL : ℝ) (block240LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block240S1 : ℝ))
    (hy2ne : y ≠ (block240S2 : ℝ))
    (hy3ne : y ≠ (block240S3 : ℝ))
    (hy4ne : y ≠ (block240S4 : ℝ)) :
    0 < block240V y := by
  have hcert := block240LeftCertificate_eq_true
  unfold block240LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block240LeftBoxes) (lo := block240LeftL) (hi := block240LeftR)
    (w1 := block240W1) (w2 := block240W2) (w3 := block240W3) (w4 := block240W4)
    (s1 := block240S1) (s2 := block240S2) (s3 := block240S3) (s4 := block240S4)
    hboxes hcover block240LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block240RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block240RightChunk000 block240W1 block240W2 block240W3 block240W4 block240S1 block240S2 block240S3 block240S4

theorem block240RightChunk000ParamsCertificate_eq_true :
    block240RightChunk000ParamsCertificate = true := by
  native_decide

theorem block240_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block240RightChunk000L : ℝ) (block240RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block240S1 : ℝ))
    (hy2ne : y ≠ (block240S2 : ℝ))
    (hy3ne : y ≠ (block240S3 : ℝ))
    (hy4ne : y ≠ (block240S4 : ℝ)) :
    0 < block240V y := by
  have hcert := block240RightChunk000Certificate_eq_true
  unfold block240RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block240RightChunk000) (lo := block240RightChunk000L) (hi := block240RightChunk000R)
    (w1 := block240W1) (w2 := block240W2) (w3 := block240W3) (w4 := block240W4)
    (s1 := block240S1) (s2 := block240S2) (s3 := block240S3) (s4 := block240S4)
    hboxes hcover block240RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block240RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block240RightChunk001 block240W1 block240W2 block240W3 block240W4 block240S1 block240S2 block240S3 block240S4

theorem block240RightChunk001ParamsCertificate_eq_true :
    block240RightChunk001ParamsCertificate = true := by
  native_decide

theorem block240_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block240RightChunk001L : ℝ) (block240RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block240S1 : ℝ))
    (hy2ne : y ≠ (block240S2 : ℝ))
    (hy3ne : y ≠ (block240S3 : ℝ))
    (hy4ne : y ≠ (block240S4 : ℝ)) :
    0 < block240V y := by
  have hcert := block240RightChunk001Certificate_eq_true
  unfold block240RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block240RightChunk001) (lo := block240RightChunk001L) (hi := block240RightChunk001R)
    (w1 := block240W1) (w2 := block240W2) (w3 := block240W3) (w4 := block240W4)
    (s1 := block240S1) (s2 := block240S2) (s3 := block240S3) (s4 := block240S4)
    hboxes hcover block240RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block240_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block240RightL : ℝ) (block240RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block240S1 : ℝ))
    (hy2ne : y ≠ (block240S2 : ℝ))
    (hy3ne : y ≠ (block240S3 : ℝ))
    (hy4ne : y ≠ (block240S4 : ℝ)) :
    0 < block240V y := by
  by_cases h0 : y ≤ (block240RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block240RightChunk000L : ℝ) (block240RightChunk000R : ℝ) := by
      have hL : (block240RightChunk000L : ℝ) = (block240RightL : ℝ) := by
        norm_num [block240RightChunk000L, block240RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block240_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block240RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block240RightChunk001L : ℝ) = (block240RightChunk000R : ℝ) := by
      norm_num [block240RightChunk001L, block240RightChunk000R]
    have hR : (block240RightChunk001R : ℝ) = (block240RightR : ℝ) := by
      norm_num [block240RightChunk001R, block240RightR]
    have hyc : y ∈ Icc (block240RightChunk001L : ℝ) (block240RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block240_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block240_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block240LeftL : ℝ) (block240LeftR : ℝ) →
    y ≠ 0 → y ≠ (block240S1 : ℝ) → y ≠ (block240S2 : ℝ) →
    y ≠ (block240S3 : ℝ) → y ≠ (block240S4 : ℝ) → 0 < block240V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block240RightL : ℝ) (block240RightR : ℝ) →
    y ≠ 0 → y ≠ (block240S1 : ℝ) → y ≠ (block240S2 : ℝ) →
    y ≠ (block240S3 : ℝ) → y ≠ (block240S4 : ℝ) → 0 < block240V y)

theorem block240_reallog_certificate_proof :
    block240_reallog_certificate := by
  exact ⟨block240_left_V_pos, block240_right_V_pos⟩

end Block240
end M1817475
end Erdos1038Lean
