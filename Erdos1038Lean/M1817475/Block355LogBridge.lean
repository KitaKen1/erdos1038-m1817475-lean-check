import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block355

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block355

open Set

def block355W1 : Rat := ((89626313619803 : Rat) / 100000000000000)
def block355W2 : Rat := ((4749648757643457 : Rat) / 100000000000000000)
def block355W3 : Rat := ((751948885933783 : Rat) / 5000000000000000)
def block355W4 : Rat := ((1732793413009431 : Rat) / 12500000000000000)
def block355S1 : Rat := ((18174751 : Rat) / 10000000)
def block355S2 : Rat := ((511587 : Rat) / 200000)
def block355S3 : Rat := ((133193624196428571453 : Rat) / 50000000000000000000)
def block355S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block355V (y : ℝ) : ℝ :=
  ratPotential block355W1 block355W2 block355W3 block355W4 block355S1 block355S2 block355S3 block355S4 y

def block355LeftParamsCertificate : Bool :=
  allBoxesSameParams block355LeftBoxes block355W1 block355W2 block355W3 block355W4 block355S1 block355S2 block355S3 block355S4

theorem block355LeftParamsCertificate_eq_true :
    block355LeftParamsCertificate = true := by
  native_decide

theorem block355_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block355LeftL : ℝ) (block355LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block355S1 : ℝ))
    (hy2ne : y ≠ (block355S2 : ℝ))
    (hy3ne : y ≠ (block355S3 : ℝ))
    (hy4ne : y ≠ (block355S4 : ℝ)) :
    0 < block355V y := by
  have hcert := block355LeftCertificate_eq_true
  unfold block355LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block355LeftBoxes) (lo := block355LeftL) (hi := block355LeftR)
    (w1 := block355W1) (w2 := block355W2) (w3 := block355W3) (w4 := block355W4)
    (s1 := block355S1) (s2 := block355S2) (s3 := block355S3) (s4 := block355S4)
    hboxes hcover block355LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block355RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block355RightChunk000 block355W1 block355W2 block355W3 block355W4 block355S1 block355S2 block355S3 block355S4

theorem block355RightChunk000ParamsCertificate_eq_true :
    block355RightChunk000ParamsCertificate = true := by
  native_decide

theorem block355_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block355RightChunk000L : ℝ) (block355RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block355S1 : ℝ))
    (hy2ne : y ≠ (block355S2 : ℝ))
    (hy3ne : y ≠ (block355S3 : ℝ))
    (hy4ne : y ≠ (block355S4 : ℝ)) :
    0 < block355V y := by
  have hcert := block355RightChunk000Certificate_eq_true
  unfold block355RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block355RightChunk000) (lo := block355RightChunk000L) (hi := block355RightChunk000R)
    (w1 := block355W1) (w2 := block355W2) (w3 := block355W3) (w4 := block355W4)
    (s1 := block355S1) (s2 := block355S2) (s3 := block355S3) (s4 := block355S4)
    hboxes hcover block355RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block355_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block355RightL : ℝ) (block355RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block355S1 : ℝ))
    (hy2ne : y ≠ (block355S2 : ℝ))
    (hy3ne : y ≠ (block355S3 : ℝ))
    (hy4ne : y ≠ (block355S4 : ℝ)) :
    0 < block355V y := by
  have hL : (block355RightChunk000L : ℝ) = (block355RightL : ℝ) := by
    norm_num [block355RightChunk000L, block355RightL]
  have hR : (block355RightChunk000R : ℝ) = (block355RightR : ℝ) := by
    norm_num [block355RightChunk000R, block355RightR]
  have hyc : y ∈ Icc (block355RightChunk000L : ℝ) (block355RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block355_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block355_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block355LeftL : ℝ) (block355LeftR : ℝ) →
    y ≠ 0 → y ≠ (block355S1 : ℝ) → y ≠ (block355S2 : ℝ) →
    y ≠ (block355S3 : ℝ) → y ≠ (block355S4 : ℝ) → 0 < block355V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block355RightL : ℝ) (block355RightR : ℝ) →
    y ≠ 0 → y ≠ (block355S1 : ℝ) → y ≠ (block355S2 : ℝ) →
    y ≠ (block355S3 : ℝ) → y ≠ (block355S4 : ℝ) → 0 < block355V y)

theorem block355_reallog_certificate_proof :
    block355_reallog_certificate := by
  exact ⟨block355_left_V_pos, block355_right_V_pos⟩

end Block355
end M1817475
end Erdos1038Lean
