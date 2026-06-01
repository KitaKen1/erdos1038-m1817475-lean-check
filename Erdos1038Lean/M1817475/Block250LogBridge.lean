import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block250

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block250

open Set

def block250W1 : Rat := ((8534341678960841 : Rat) / 10000000000000000)
def block250W2 : Rat := ((1761146843623659 : Rat) / 20000000000000000)
def block250W3 : Rat := ((9882851343953479 : Rat) / 200000000000000000)
def block250W4 : Rat := ((19906409756983923 : Rat) / 100000000000000000)
def block250S1 : Rat := ((18174751 : Rat) / 10000000)
def block250S2 : Rat := ((511587 : Rat) / 200000)
def block250S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block250S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block250V (y : ℝ) : ℝ :=
  ratPotential block250W1 block250W2 block250W3 block250W4 block250S1 block250S2 block250S3 block250S4 y

def block250LeftParamsCertificate : Bool :=
  allBoxesSameParams block250LeftBoxes block250W1 block250W2 block250W3 block250W4 block250S1 block250S2 block250S3 block250S4

theorem block250LeftParamsCertificate_eq_true :
    block250LeftParamsCertificate = true := by
  native_decide

theorem block250_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block250LeftL : ℝ) (block250LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block250S1 : ℝ))
    (hy2ne : y ≠ (block250S2 : ℝ))
    (hy3ne : y ≠ (block250S3 : ℝ))
    (hy4ne : y ≠ (block250S4 : ℝ)) :
    0 < block250V y := by
  have hcert := block250LeftCertificate_eq_true
  unfold block250LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block250LeftBoxes) (lo := block250LeftL) (hi := block250LeftR)
    (w1 := block250W1) (w2 := block250W2) (w3 := block250W3) (w4 := block250W4)
    (s1 := block250S1) (s2 := block250S2) (s3 := block250S3) (s4 := block250S4)
    hboxes hcover block250LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block250RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block250RightChunk000 block250W1 block250W2 block250W3 block250W4 block250S1 block250S2 block250S3 block250S4

theorem block250RightChunk000ParamsCertificate_eq_true :
    block250RightChunk000ParamsCertificate = true := by
  native_decide

theorem block250_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block250RightChunk000L : ℝ) (block250RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block250S1 : ℝ))
    (hy2ne : y ≠ (block250S2 : ℝ))
    (hy3ne : y ≠ (block250S3 : ℝ))
    (hy4ne : y ≠ (block250S4 : ℝ)) :
    0 < block250V y := by
  have hcert := block250RightChunk000Certificate_eq_true
  unfold block250RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block250RightChunk000) (lo := block250RightChunk000L) (hi := block250RightChunk000R)
    (w1 := block250W1) (w2 := block250W2) (w3 := block250W3) (w4 := block250W4)
    (s1 := block250S1) (s2 := block250S2) (s3 := block250S3) (s4 := block250S4)
    hboxes hcover block250RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block250_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block250RightL : ℝ) (block250RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block250S1 : ℝ))
    (hy2ne : y ≠ (block250S2 : ℝ))
    (hy3ne : y ≠ (block250S3 : ℝ))
    (hy4ne : y ≠ (block250S4 : ℝ)) :
    0 < block250V y := by
  have hL : (block250RightChunk000L : ℝ) = (block250RightL : ℝ) := by
    norm_num [block250RightChunk000L, block250RightL]
  have hR : (block250RightChunk000R : ℝ) = (block250RightR : ℝ) := by
    norm_num [block250RightChunk000R, block250RightR]
  have hyc : y ∈ Icc (block250RightChunk000L : ℝ) (block250RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block250_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block250_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block250LeftL : ℝ) (block250LeftR : ℝ) →
    y ≠ 0 → y ≠ (block250S1 : ℝ) → y ≠ (block250S2 : ℝ) →
    y ≠ (block250S3 : ℝ) → y ≠ (block250S4 : ℝ) → 0 < block250V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block250RightL : ℝ) (block250RightR : ℝ) →
    y ≠ 0 → y ≠ (block250S1 : ℝ) → y ≠ (block250S2 : ℝ) →
    y ≠ (block250S3 : ℝ) → y ≠ (block250S4 : ℝ) → 0 < block250V y)

theorem block250_reallog_certificate_proof :
    block250_reallog_certificate := by
  exact ⟨block250_left_V_pos, block250_right_V_pos⟩

end Block250
end M1817475
end Erdos1038Lean
