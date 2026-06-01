import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block080

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block080

open Set

def block080W1 : Rat := ((33273632990275033 : Rat) / 10000000000000000)
def block080W2 : Rat := (0 : Rat)
def block080W3 : Rat := (0 : Rat)
def block080W4 : Rat := ((1209802394919259 : Rat) / 5000000000000000)
def block080S1 : Rat := ((18174751 : Rat) / 10000000)
def block080S2 : Rat := ((511587 : Rat) / 200000)
def block080S3 : Rat := ((107000619 : Rat) / 40000000)
def block080S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block080V (y : ℝ) : ℝ :=
  ratPotential block080W1 block080W2 block080W3 block080W4 block080S1 block080S2 block080S3 block080S4 y

def block080LeftParamsCertificate : Bool :=
  allBoxesSameParams block080LeftBoxes block080W1 block080W2 block080W3 block080W4 block080S1 block080S2 block080S3 block080S4

theorem block080LeftParamsCertificate_eq_true :
    block080LeftParamsCertificate = true := by
  native_decide

theorem block080_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block080LeftL : ℝ) (block080LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block080S1 : ℝ))
    (hy2ne : y ≠ (block080S2 : ℝ))
    (hy3ne : y ≠ (block080S3 : ℝ))
    (hy4ne : y ≠ (block080S4 : ℝ)) :
    0 < block080V y := by
  have hcert := block080LeftCertificate_eq_true
  unfold block080LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block080LeftBoxes) (lo := block080LeftL) (hi := block080LeftR)
    (w1 := block080W1) (w2 := block080W2) (w3 := block080W3) (w4 := block080W4)
    (s1 := block080S1) (s2 := block080S2) (s3 := block080S3) (s4 := block080S4)
    hboxes hcover block080LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block080RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block080RightChunk000 block080W1 block080W2 block080W3 block080W4 block080S1 block080S2 block080S3 block080S4

theorem block080RightChunk000ParamsCertificate_eq_true :
    block080RightChunk000ParamsCertificate = true := by
  native_decide

theorem block080_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block080RightChunk000L : ℝ) (block080RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block080S1 : ℝ))
    (hy2ne : y ≠ (block080S2 : ℝ))
    (hy3ne : y ≠ (block080S3 : ℝ))
    (hy4ne : y ≠ (block080S4 : ℝ)) :
    0 < block080V y := by
  have hcert := block080RightChunk000Certificate_eq_true
  unfold block080RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block080RightChunk000) (lo := block080RightChunk000L) (hi := block080RightChunk000R)
    (w1 := block080W1) (w2 := block080W2) (w3 := block080W3) (w4 := block080W4)
    (s1 := block080S1) (s2 := block080S2) (s3 := block080S3) (s4 := block080S4)
    hboxes hcover block080RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block080_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block080RightL : ℝ) (block080RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block080S1 : ℝ))
    (hy2ne : y ≠ (block080S2 : ℝ))
    (hy3ne : y ≠ (block080S3 : ℝ))
    (hy4ne : y ≠ (block080S4 : ℝ)) :
    0 < block080V y := by
  have hL : (block080RightChunk000L : ℝ) = (block080RightL : ℝ) := by
    norm_num [block080RightChunk000L, block080RightL]
  have hR : (block080RightChunk000R : ℝ) = (block080RightR : ℝ) := by
    norm_num [block080RightChunk000R, block080RightR]
  have hyc : y ∈ Icc (block080RightChunk000L : ℝ) (block080RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block080_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block080_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block080LeftL : ℝ) (block080LeftR : ℝ) →
    y ≠ 0 → y ≠ (block080S1 : ℝ) → y ≠ (block080S2 : ℝ) →
    y ≠ (block080S3 : ℝ) → y ≠ (block080S4 : ℝ) → 0 < block080V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block080RightL : ℝ) (block080RightR : ℝ) →
    y ≠ 0 → y ≠ (block080S1 : ℝ) → y ≠ (block080S2 : ℝ) →
    y ≠ (block080S3 : ℝ) → y ≠ (block080S4 : ℝ) → 0 < block080V y)

theorem block080_reallog_certificate_proof :
    block080_reallog_certificate := by
  exact ⟨block080_left_V_pos, block080_right_V_pos⟩

end Block080
end M1817475
end Erdos1038Lean
