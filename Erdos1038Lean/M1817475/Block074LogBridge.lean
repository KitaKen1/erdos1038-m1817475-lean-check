import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block074

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block074

open Set

def block074W1 : Rat := ((31725048180534823 : Rat) / 10000000000000000)
def block074W2 : Rat := (0 : Rat)
def block074W3 : Rat := (0 : Rat)
def block074W4 : Rat := ((12389592850321289 : Rat) / 50000000000000000)
def block074S1 : Rat := ((18174751 : Rat) / 10000000)
def block074S2 : Rat := ((511587 : Rat) / 200000)
def block074S3 : Rat := ((107000619 : Rat) / 40000000)
def block074S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block074V (y : ℝ) : ℝ :=
  ratPotential block074W1 block074W2 block074W3 block074W4 block074S1 block074S2 block074S3 block074S4 y

def block074LeftParamsCertificate : Bool :=
  allBoxesSameParams block074LeftBoxes block074W1 block074W2 block074W3 block074W4 block074S1 block074S2 block074S3 block074S4

theorem block074LeftParamsCertificate_eq_true :
    block074LeftParamsCertificate = true := by
  native_decide

theorem block074_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block074LeftL : ℝ) (block074LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block074S1 : ℝ))
    (hy2ne : y ≠ (block074S2 : ℝ))
    (hy3ne : y ≠ (block074S3 : ℝ))
    (hy4ne : y ≠ (block074S4 : ℝ)) :
    0 < block074V y := by
  have hcert := block074LeftCertificate_eq_true
  unfold block074LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block074LeftBoxes) (lo := block074LeftL) (hi := block074LeftR)
    (w1 := block074W1) (w2 := block074W2) (w3 := block074W3) (w4 := block074W4)
    (s1 := block074S1) (s2 := block074S2) (s3 := block074S3) (s4 := block074S4)
    hboxes hcover block074LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block074RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block074RightChunk000 block074W1 block074W2 block074W3 block074W4 block074S1 block074S2 block074S3 block074S4

theorem block074RightChunk000ParamsCertificate_eq_true :
    block074RightChunk000ParamsCertificate = true := by
  native_decide

theorem block074_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block074RightChunk000L : ℝ) (block074RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block074S1 : ℝ))
    (hy2ne : y ≠ (block074S2 : ℝ))
    (hy3ne : y ≠ (block074S3 : ℝ))
    (hy4ne : y ≠ (block074S4 : ℝ)) :
    0 < block074V y := by
  have hcert := block074RightChunk000Certificate_eq_true
  unfold block074RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block074RightChunk000) (lo := block074RightChunk000L) (hi := block074RightChunk000R)
    (w1 := block074W1) (w2 := block074W2) (w3 := block074W3) (w4 := block074W4)
    (s1 := block074S1) (s2 := block074S2) (s3 := block074S3) (s4 := block074S4)
    hboxes hcover block074RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block074_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block074RightL : ℝ) (block074RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block074S1 : ℝ))
    (hy2ne : y ≠ (block074S2 : ℝ))
    (hy3ne : y ≠ (block074S3 : ℝ))
    (hy4ne : y ≠ (block074S4 : ℝ)) :
    0 < block074V y := by
  have hL : (block074RightChunk000L : ℝ) = (block074RightL : ℝ) := by
    norm_num [block074RightChunk000L, block074RightL]
  have hR : (block074RightChunk000R : ℝ) = (block074RightR : ℝ) := by
    norm_num [block074RightChunk000R, block074RightR]
  have hyc : y ∈ Icc (block074RightChunk000L : ℝ) (block074RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block074_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block074_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block074LeftL : ℝ) (block074LeftR : ℝ) →
    y ≠ 0 → y ≠ (block074S1 : ℝ) → y ≠ (block074S2 : ℝ) →
    y ≠ (block074S3 : ℝ) → y ≠ (block074S4 : ℝ) → 0 < block074V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block074RightL : ℝ) (block074RightR : ℝ) →
    y ≠ 0 → y ≠ (block074S1 : ℝ) → y ≠ (block074S2 : ℝ) →
    y ≠ (block074S3 : ℝ) → y ≠ (block074S4 : ℝ) → 0 < block074V y)

theorem block074_reallog_certificate_proof :
    block074_reallog_certificate := by
  exact ⟨block074_left_V_pos, block074_right_V_pos⟩

end Block074
end M1817475
end Erdos1038Lean
