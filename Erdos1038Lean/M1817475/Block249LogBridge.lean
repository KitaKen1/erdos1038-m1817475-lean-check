import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block249

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block249

open Set

def block249W1 : Rat := ((8542194945336559 : Rat) / 10000000000000000)
def block249W2 : Rat := ((8759869899595991 : Rat) / 100000000000000000)
def block249W3 : Rat := ((4796737962231183 : Rat) / 100000000000000000)
def block249W4 : Rat := ((20099213010708097 : Rat) / 100000000000000000)
def block249S1 : Rat := ((18174751 : Rat) / 10000000)
def block249S2 : Rat := ((511587 : Rat) / 200000)
def block249S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block249S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block249V (y : ℝ) : ℝ :=
  ratPotential block249W1 block249W2 block249W3 block249W4 block249S1 block249S2 block249S3 block249S4 y

def block249LeftParamsCertificate : Bool :=
  allBoxesSameParams block249LeftBoxes block249W1 block249W2 block249W3 block249W4 block249S1 block249S2 block249S3 block249S4

theorem block249LeftParamsCertificate_eq_true :
    block249LeftParamsCertificate = true := by
  native_decide

theorem block249_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block249LeftL : ℝ) (block249LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block249S1 : ℝ))
    (hy2ne : y ≠ (block249S2 : ℝ))
    (hy3ne : y ≠ (block249S3 : ℝ))
    (hy4ne : y ≠ (block249S4 : ℝ)) :
    0 < block249V y := by
  have hcert := block249LeftCertificate_eq_true
  unfold block249LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block249LeftBoxes) (lo := block249LeftL) (hi := block249LeftR)
    (w1 := block249W1) (w2 := block249W2) (w3 := block249W3) (w4 := block249W4)
    (s1 := block249S1) (s2 := block249S2) (s3 := block249S3) (s4 := block249S4)
    hboxes hcover block249LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block249RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block249RightChunk000 block249W1 block249W2 block249W3 block249W4 block249S1 block249S2 block249S3 block249S4

theorem block249RightChunk000ParamsCertificate_eq_true :
    block249RightChunk000ParamsCertificate = true := by
  native_decide

theorem block249_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block249RightChunk000L : ℝ) (block249RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block249S1 : ℝ))
    (hy2ne : y ≠ (block249S2 : ℝ))
    (hy3ne : y ≠ (block249S3 : ℝ))
    (hy4ne : y ≠ (block249S4 : ℝ)) :
    0 < block249V y := by
  have hcert := block249RightChunk000Certificate_eq_true
  unfold block249RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block249RightChunk000) (lo := block249RightChunk000L) (hi := block249RightChunk000R)
    (w1 := block249W1) (w2 := block249W2) (w3 := block249W3) (w4 := block249W4)
    (s1 := block249S1) (s2 := block249S2) (s3 := block249S3) (s4 := block249S4)
    hboxes hcover block249RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block249_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block249RightL : ℝ) (block249RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block249S1 : ℝ))
    (hy2ne : y ≠ (block249S2 : ℝ))
    (hy3ne : y ≠ (block249S3 : ℝ))
    (hy4ne : y ≠ (block249S4 : ℝ)) :
    0 < block249V y := by
  have hL : (block249RightChunk000L : ℝ) = (block249RightL : ℝ) := by
    norm_num [block249RightChunk000L, block249RightL]
  have hR : (block249RightChunk000R : ℝ) = (block249RightR : ℝ) := by
    norm_num [block249RightChunk000R, block249RightR]
  have hyc : y ∈ Icc (block249RightChunk000L : ℝ) (block249RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block249_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block249_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block249LeftL : ℝ) (block249LeftR : ℝ) →
    y ≠ 0 → y ≠ (block249S1 : ℝ) → y ≠ (block249S2 : ℝ) →
    y ≠ (block249S3 : ℝ) → y ≠ (block249S4 : ℝ) → 0 < block249V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block249RightL : ℝ) (block249RightR : ℝ) →
    y ≠ 0 → y ≠ (block249S1 : ℝ) → y ≠ (block249S2 : ℝ) →
    y ≠ (block249S3 : ℝ) → y ≠ (block249S4 : ℝ) → 0 < block249V y)

theorem block249_reallog_certificate_proof :
    block249_reallog_certificate := by
  exact ⟨block249_left_V_pos, block249_right_V_pos⟩

end Block249
end M1817475
end Erdos1038Lean
