import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block327

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block327

open Set

def block327W1 : Rat := ((1196447208144759 : Rat) / 1250000000000000)
def block327W2 : Rat := ((944574330251137 : Rat) / 20000000000000000)
def block327W3 : Rat := ((1423210296770627 : Rat) / 10000000000000000)
def block327W4 : Rat := ((27317329996433 : Rat) / 200000000000000)
def block327S1 : Rat := ((18174751 : Rat) / 10000000)
def block327S2 : Rat := ((511587 : Rat) / 200000)
def block327S3 : Rat := ((107000619 : Rat) / 40000000)
def block327S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block327V (y : ℝ) : ℝ :=
  ratPotential block327W1 block327W2 block327W3 block327W4 block327S1 block327S2 block327S3 block327S4 y

def block327LeftParamsCertificate : Bool :=
  allBoxesSameParams block327LeftBoxes block327W1 block327W2 block327W3 block327W4 block327S1 block327S2 block327S3 block327S4

theorem block327LeftParamsCertificate_eq_true :
    block327LeftParamsCertificate = true := by
  native_decide

theorem block327_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block327LeftL : ℝ) (block327LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block327S1 : ℝ))
    (hy2ne : y ≠ (block327S2 : ℝ))
    (hy3ne : y ≠ (block327S3 : ℝ))
    (hy4ne : y ≠ (block327S4 : ℝ)) :
    0 < block327V y := by
  have hcert := block327LeftCertificate_eq_true
  unfold block327LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block327LeftBoxes) (lo := block327LeftL) (hi := block327LeftR)
    (w1 := block327W1) (w2 := block327W2) (w3 := block327W3) (w4 := block327W4)
    (s1 := block327S1) (s2 := block327S2) (s3 := block327S3) (s4 := block327S4)
    hboxes hcover block327LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block327RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block327RightChunk000 block327W1 block327W2 block327W3 block327W4 block327S1 block327S2 block327S3 block327S4

theorem block327RightChunk000ParamsCertificate_eq_true :
    block327RightChunk000ParamsCertificate = true := by
  native_decide

theorem block327_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block327RightChunk000L : ℝ) (block327RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block327S1 : ℝ))
    (hy2ne : y ≠ (block327S2 : ℝ))
    (hy3ne : y ≠ (block327S3 : ℝ))
    (hy4ne : y ≠ (block327S4 : ℝ)) :
    0 < block327V y := by
  have hcert := block327RightChunk000Certificate_eq_true
  unfold block327RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block327RightChunk000) (lo := block327RightChunk000L) (hi := block327RightChunk000R)
    (w1 := block327W1) (w2 := block327W2) (w3 := block327W3) (w4 := block327W4)
    (s1 := block327S1) (s2 := block327S2) (s3 := block327S3) (s4 := block327S4)
    hboxes hcover block327RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block327_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block327RightL : ℝ) (block327RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block327S1 : ℝ))
    (hy2ne : y ≠ (block327S2 : ℝ))
    (hy3ne : y ≠ (block327S3 : ℝ))
    (hy4ne : y ≠ (block327S4 : ℝ)) :
    0 < block327V y := by
  have hL : (block327RightChunk000L : ℝ) = (block327RightL : ℝ) := by
    norm_num [block327RightChunk000L, block327RightL]
  have hR : (block327RightChunk000R : ℝ) = (block327RightR : ℝ) := by
    norm_num [block327RightChunk000R, block327RightR]
  have hyc : y ∈ Icc (block327RightChunk000L : ℝ) (block327RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block327_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block327_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block327LeftL : ℝ) (block327LeftR : ℝ) →
    y ≠ 0 → y ≠ (block327S1 : ℝ) → y ≠ (block327S2 : ℝ) →
    y ≠ (block327S3 : ℝ) → y ≠ (block327S4 : ℝ) → 0 < block327V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block327RightL : ℝ) (block327RightR : ℝ) →
    y ≠ 0 → y ≠ (block327S1 : ℝ) → y ≠ (block327S2 : ℝ) →
    y ≠ (block327S3 : ℝ) → y ≠ (block327S4 : ℝ) → 0 < block327V y)

theorem block327_reallog_certificate_proof :
    block327_reallog_certificate := by
  exact ⟨block327_left_V_pos, block327_right_V_pos⟩

end Block327
end M1817475
end Erdos1038Lean
