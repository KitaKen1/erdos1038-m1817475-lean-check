import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block285

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block285

open Set

def block285W1 : Rat := ((1028613654336729 : Rat) / 1000000000000000)
def block285W2 : Rat := ((71044451956001 : Rat) / 2000000000000000)
def block285W3 : Rat := ((28308181626538087 : Rat) / 100000000000000000)
def block285W4 : Rat := (0 : Rat)
def block285S1 : Rat := ((18174751 : Rat) / 10000000)
def block285S2 : Rat := ((511587 : Rat) / 200000)
def block285S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block285S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block285V (y : ℝ) : ℝ :=
  ratPotential block285W1 block285W2 block285W3 block285W4 block285S1 block285S2 block285S3 block285S4 y

def block285LeftParamsCertificate : Bool :=
  allBoxesSameParams block285LeftBoxes block285W1 block285W2 block285W3 block285W4 block285S1 block285S2 block285S3 block285S4

theorem block285LeftParamsCertificate_eq_true :
    block285LeftParamsCertificate = true := by
  native_decide

theorem block285_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block285LeftL : ℝ) (block285LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block285S1 : ℝ))
    (hy2ne : y ≠ (block285S2 : ℝ))
    (hy3ne : y ≠ (block285S3 : ℝ))
    (hy4ne : y ≠ (block285S4 : ℝ)) :
    0 < block285V y := by
  have hcert := block285LeftCertificate_eq_true
  unfold block285LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block285LeftBoxes) (lo := block285LeftL) (hi := block285LeftR)
    (w1 := block285W1) (w2 := block285W2) (w3 := block285W3) (w4 := block285W4)
    (s1 := block285S1) (s2 := block285S2) (s3 := block285S3) (s4 := block285S4)
    hboxes hcover block285LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block285RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block285RightChunk000 block285W1 block285W2 block285W3 block285W4 block285S1 block285S2 block285S3 block285S4

theorem block285RightChunk000ParamsCertificate_eq_true :
    block285RightChunk000ParamsCertificate = true := by
  native_decide

theorem block285_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block285RightChunk000L : ℝ) (block285RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block285S1 : ℝ))
    (hy2ne : y ≠ (block285S2 : ℝ))
    (hy3ne : y ≠ (block285S3 : ℝ))
    (hy4ne : y ≠ (block285S4 : ℝ)) :
    0 < block285V y := by
  have hcert := block285RightChunk000Certificate_eq_true
  unfold block285RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block285RightChunk000) (lo := block285RightChunk000L) (hi := block285RightChunk000R)
    (w1 := block285W1) (w2 := block285W2) (w3 := block285W3) (w4 := block285W4)
    (s1 := block285S1) (s2 := block285S2) (s3 := block285S3) (s4 := block285S4)
    hboxes hcover block285RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block285_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block285RightL : ℝ) (block285RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block285S1 : ℝ))
    (hy2ne : y ≠ (block285S2 : ℝ))
    (hy3ne : y ≠ (block285S3 : ℝ))
    (hy4ne : y ≠ (block285S4 : ℝ)) :
    0 < block285V y := by
  have hL : (block285RightChunk000L : ℝ) = (block285RightL : ℝ) := by
    norm_num [block285RightChunk000L, block285RightL]
  have hR : (block285RightChunk000R : ℝ) = (block285RightR : ℝ) := by
    norm_num [block285RightChunk000R, block285RightR]
  have hyc : y ∈ Icc (block285RightChunk000L : ℝ) (block285RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block285_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block285_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block285LeftL : ℝ) (block285LeftR : ℝ) →
    y ≠ 0 → y ≠ (block285S1 : ℝ) → y ≠ (block285S2 : ℝ) →
    y ≠ (block285S3 : ℝ) → y ≠ (block285S4 : ℝ) → 0 < block285V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block285RightL : ℝ) (block285RightR : ℝ) →
    y ≠ 0 → y ≠ (block285S1 : ℝ) → y ≠ (block285S2 : ℝ) →
    y ≠ (block285S3 : ℝ) → y ≠ (block285S4 : ℝ) → 0 < block285V y)

theorem block285_reallog_certificate_proof :
    block285_reallog_certificate := by
  exact ⟨block285_left_V_pos, block285_right_V_pos⟩

end Block285
end M1817475
end Erdos1038Lean
