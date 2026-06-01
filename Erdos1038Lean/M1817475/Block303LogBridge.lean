import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block303

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block303

open Set

def block303W1 : Rat := ((990483898358703 : Rat) / 1000000000000000)
def block303W2 : Rat := ((12593550145457249 : Rat) / 250000000000000000)
def block303W3 : Rat := ((268266814304319 : Rat) / 1000000000000000)
def block303W4 : Rat := (0 : Rat)
def block303S1 : Rat := ((18174751 : Rat) / 10000000)
def block303S2 : Rat := ((511587 : Rat) / 200000)
def block303S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block303S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block303V (y : ℝ) : ℝ :=
  ratPotential block303W1 block303W2 block303W3 block303W4 block303S1 block303S2 block303S3 block303S4 y

def block303LeftParamsCertificate : Bool :=
  allBoxesSameParams block303LeftBoxes block303W1 block303W2 block303W3 block303W4 block303S1 block303S2 block303S3 block303S4

theorem block303LeftParamsCertificate_eq_true :
    block303LeftParamsCertificate = true := by
  native_decide

theorem block303_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block303LeftL : ℝ) (block303LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block303S1 : ℝ))
    (hy2ne : y ≠ (block303S2 : ℝ))
    (hy3ne : y ≠ (block303S3 : ℝ))
    (hy4ne : y ≠ (block303S4 : ℝ)) :
    0 < block303V y := by
  have hcert := block303LeftCertificate_eq_true
  unfold block303LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block303LeftBoxes) (lo := block303LeftL) (hi := block303LeftR)
    (w1 := block303W1) (w2 := block303W2) (w3 := block303W3) (w4 := block303W4)
    (s1 := block303S1) (s2 := block303S2) (s3 := block303S3) (s4 := block303S4)
    hboxes hcover block303LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block303RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block303RightChunk000 block303W1 block303W2 block303W3 block303W4 block303S1 block303S2 block303S3 block303S4

theorem block303RightChunk000ParamsCertificate_eq_true :
    block303RightChunk000ParamsCertificate = true := by
  native_decide

theorem block303_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block303RightChunk000L : ℝ) (block303RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block303S1 : ℝ))
    (hy2ne : y ≠ (block303S2 : ℝ))
    (hy3ne : y ≠ (block303S3 : ℝ))
    (hy4ne : y ≠ (block303S4 : ℝ)) :
    0 < block303V y := by
  have hcert := block303RightChunk000Certificate_eq_true
  unfold block303RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block303RightChunk000) (lo := block303RightChunk000L) (hi := block303RightChunk000R)
    (w1 := block303W1) (w2 := block303W2) (w3 := block303W3) (w4 := block303W4)
    (s1 := block303S1) (s2 := block303S2) (s3 := block303S3) (s4 := block303S4)
    hboxes hcover block303RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block303_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block303RightL : ℝ) (block303RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block303S1 : ℝ))
    (hy2ne : y ≠ (block303S2 : ℝ))
    (hy3ne : y ≠ (block303S3 : ℝ))
    (hy4ne : y ≠ (block303S4 : ℝ)) :
    0 < block303V y := by
  have hL : (block303RightChunk000L : ℝ) = (block303RightL : ℝ) := by
    norm_num [block303RightChunk000L, block303RightL]
  have hR : (block303RightChunk000R : ℝ) = (block303RightR : ℝ) := by
    norm_num [block303RightChunk000R, block303RightR]
  have hyc : y ∈ Icc (block303RightChunk000L : ℝ) (block303RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block303_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block303_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block303LeftL : ℝ) (block303LeftR : ℝ) →
    y ≠ 0 → y ≠ (block303S1 : ℝ) → y ≠ (block303S2 : ℝ) →
    y ≠ (block303S3 : ℝ) → y ≠ (block303S4 : ℝ) → 0 < block303V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block303RightL : ℝ) (block303RightR : ℝ) →
    y ≠ 0 → y ≠ (block303S1 : ℝ) → y ≠ (block303S2 : ℝ) →
    y ≠ (block303S3 : ℝ) → y ≠ (block303S4 : ℝ) → 0 < block303V y)

theorem block303_reallog_certificate_proof :
    block303_reallog_certificate := by
  exact ⟨block303_left_V_pos, block303_right_V_pos⟩

end Block303
end M1817475
end Erdos1038Lean
