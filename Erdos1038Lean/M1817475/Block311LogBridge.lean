import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block311

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block311

open Set

def block311W1 : Rat := ((967505624255229 : Rat) / 1000000000000000)
def block311W2 : Rat := ((29298022445385187 : Rat) / 500000000000000000)
def block311W3 : Rat := ((5220172078946631 : Rat) / 20000000000000000)
def block311W4 : Rat := (0 : Rat)
def block311S1 : Rat := ((18174751 : Rat) / 10000000)
def block311S2 : Rat := ((511587 : Rat) / 200000)
def block311S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block311S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block311V (y : ℝ) : ℝ :=
  ratPotential block311W1 block311W2 block311W3 block311W4 block311S1 block311S2 block311S3 block311S4 y

def block311LeftParamsCertificate : Bool :=
  allBoxesSameParams block311LeftBoxes block311W1 block311W2 block311W3 block311W4 block311S1 block311S2 block311S3 block311S4

theorem block311LeftParamsCertificate_eq_true :
    block311LeftParamsCertificate = true := by
  native_decide

theorem block311_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block311LeftL : ℝ) (block311LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block311S1 : ℝ))
    (hy2ne : y ≠ (block311S2 : ℝ))
    (hy3ne : y ≠ (block311S3 : ℝ))
    (hy4ne : y ≠ (block311S4 : ℝ)) :
    0 < block311V y := by
  have hcert := block311LeftCertificate_eq_true
  unfold block311LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block311LeftBoxes) (lo := block311LeftL) (hi := block311LeftR)
    (w1 := block311W1) (w2 := block311W2) (w3 := block311W3) (w4 := block311W4)
    (s1 := block311S1) (s2 := block311S2) (s3 := block311S3) (s4 := block311S4)
    hboxes hcover block311LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block311RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block311RightChunk000 block311W1 block311W2 block311W3 block311W4 block311S1 block311S2 block311S3 block311S4

theorem block311RightChunk000ParamsCertificate_eq_true :
    block311RightChunk000ParamsCertificate = true := by
  native_decide

theorem block311_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block311RightChunk000L : ℝ) (block311RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block311S1 : ℝ))
    (hy2ne : y ≠ (block311S2 : ℝ))
    (hy3ne : y ≠ (block311S3 : ℝ))
    (hy4ne : y ≠ (block311S4 : ℝ)) :
    0 < block311V y := by
  have hcert := block311RightChunk000Certificate_eq_true
  unfold block311RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block311RightChunk000) (lo := block311RightChunk000L) (hi := block311RightChunk000R)
    (w1 := block311W1) (w2 := block311W2) (w3 := block311W3) (w4 := block311W4)
    (s1 := block311S1) (s2 := block311S2) (s3 := block311S3) (s4 := block311S4)
    hboxes hcover block311RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block311_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block311RightL : ℝ) (block311RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block311S1 : ℝ))
    (hy2ne : y ≠ (block311S2 : ℝ))
    (hy3ne : y ≠ (block311S3 : ℝ))
    (hy4ne : y ≠ (block311S4 : ℝ)) :
    0 < block311V y := by
  have hL : (block311RightChunk000L : ℝ) = (block311RightL : ℝ) := by
    norm_num [block311RightChunk000L, block311RightL]
  have hR : (block311RightChunk000R : ℝ) = (block311RightR : ℝ) := by
    norm_num [block311RightChunk000R, block311RightR]
  have hyc : y ∈ Icc (block311RightChunk000L : ℝ) (block311RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block311_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block311_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block311LeftL : ℝ) (block311LeftR : ℝ) →
    y ≠ 0 → y ≠ (block311S1 : ℝ) → y ≠ (block311S2 : ℝ) →
    y ≠ (block311S3 : ℝ) → y ≠ (block311S4 : ℝ) → 0 < block311V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block311RightL : ℝ) (block311RightR : ℝ) →
    y ≠ 0 → y ≠ (block311S1 : ℝ) → y ≠ (block311S2 : ℝ) →
    y ≠ (block311S3 : ℝ) → y ≠ (block311S4 : ℝ) → 0 < block311V y)

theorem block311_reallog_certificate_proof :
    block311_reallog_certificate := by
  exact ⟨block311_left_V_pos, block311_right_V_pos⟩

end Block311
end M1817475
end Erdos1038Lean
