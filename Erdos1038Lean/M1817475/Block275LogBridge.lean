import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block275

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block275

open Set

def block275W1 : Rat := ((514328062518277 : Rat) / 500000000000000)
def block275W2 : Rat := ((7806431617717641 : Rat) / 250000000000000000)
def block275W3 : Rat := ((2897208578725361 : Rat) / 10000000000000000)
def block275W4 : Rat := (0 : Rat)
def block275S1 : Rat := ((18174751 : Rat) / 10000000)
def block275S2 : Rat := ((511587 : Rat) / 200000)
def block275S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block275S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block275V (y : ℝ) : ℝ :=
  ratPotential block275W1 block275W2 block275W3 block275W4 block275S1 block275S2 block275S3 block275S4 y

def block275LeftParamsCertificate : Bool :=
  allBoxesSameParams block275LeftBoxes block275W1 block275W2 block275W3 block275W4 block275S1 block275S2 block275S3 block275S4

theorem block275LeftParamsCertificate_eq_true :
    block275LeftParamsCertificate = true := by
  native_decide

theorem block275_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block275LeftL : ℝ) (block275LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block275S1 : ℝ))
    (hy2ne : y ≠ (block275S2 : ℝ))
    (hy3ne : y ≠ (block275S3 : ℝ))
    (hy4ne : y ≠ (block275S4 : ℝ)) :
    0 < block275V y := by
  have hcert := block275LeftCertificate_eq_true
  unfold block275LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block275LeftBoxes) (lo := block275LeftL) (hi := block275LeftR)
    (w1 := block275W1) (w2 := block275W2) (w3 := block275W3) (w4 := block275W4)
    (s1 := block275S1) (s2 := block275S2) (s3 := block275S3) (s4 := block275S4)
    hboxes hcover block275LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block275RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block275RightChunk000 block275W1 block275W2 block275W3 block275W4 block275S1 block275S2 block275S3 block275S4

theorem block275RightChunk000ParamsCertificate_eq_true :
    block275RightChunk000ParamsCertificate = true := by
  native_decide

theorem block275_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block275RightChunk000L : ℝ) (block275RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block275S1 : ℝ))
    (hy2ne : y ≠ (block275S2 : ℝ))
    (hy3ne : y ≠ (block275S3 : ℝ))
    (hy4ne : y ≠ (block275S4 : ℝ)) :
    0 < block275V y := by
  have hcert := block275RightChunk000Certificate_eq_true
  unfold block275RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block275RightChunk000) (lo := block275RightChunk000L) (hi := block275RightChunk000R)
    (w1 := block275W1) (w2 := block275W2) (w3 := block275W3) (w4 := block275W4)
    (s1 := block275S1) (s2 := block275S2) (s3 := block275S3) (s4 := block275S4)
    hboxes hcover block275RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block275_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block275RightL : ℝ) (block275RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block275S1 : ℝ))
    (hy2ne : y ≠ (block275S2 : ℝ))
    (hy3ne : y ≠ (block275S3 : ℝ))
    (hy4ne : y ≠ (block275S4 : ℝ)) :
    0 < block275V y := by
  have hL : (block275RightChunk000L : ℝ) = (block275RightL : ℝ) := by
    norm_num [block275RightChunk000L, block275RightL]
  have hR : (block275RightChunk000R : ℝ) = (block275RightR : ℝ) := by
    norm_num [block275RightChunk000R, block275RightR]
  have hyc : y ∈ Icc (block275RightChunk000L : ℝ) (block275RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block275_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block275_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block275LeftL : ℝ) (block275LeftR : ℝ) →
    y ≠ 0 → y ≠ (block275S1 : ℝ) → y ≠ (block275S2 : ℝ) →
    y ≠ (block275S3 : ℝ) → y ≠ (block275S4 : ℝ) → 0 < block275V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block275RightL : ℝ) (block275RightR : ℝ) →
    y ≠ 0 → y ≠ (block275S1 : ℝ) → y ≠ (block275S2 : ℝ) →
    y ≠ (block275S3 : ℝ) → y ≠ (block275S4 : ℝ) → 0 < block275V y)

theorem block275_reallog_certificate_proof :
    block275_reallog_certificate := by
  exact ⟨block275_left_V_pos, block275_right_V_pos⟩

end Block275
end M1817475
end Erdos1038Lean
