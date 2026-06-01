import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block466

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block466

open Set

def block466W1 : Rat := ((690638019429417 : Rat) / 1250000000000000)
def block466W2 : Rat := (0 : Rat)
def block466W3 : Rat := ((17791792234949677 : Rat) / 50000000000000000)
def block466W4 : Rat := ((1370093149028721 : Rat) / 25000000000000000)
def block466S1 : Rat := ((18174751 : Rat) / 10000000)
def block466S2 : Rat := ((511587 : Rat) / 200000)
def block466S3 : Rat := ((131023673303571428691 : Rat) / 50000000000000000000)
def block466S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block466V (y : ℝ) : ℝ :=
  ratPotential block466W1 block466W2 block466W3 block466W4 block466S1 block466S2 block466S3 block466S4 y

def block466LeftParamsCertificate : Bool :=
  allBoxesSameParams block466LeftBoxes block466W1 block466W2 block466W3 block466W4 block466S1 block466S2 block466S3 block466S4

theorem block466LeftParamsCertificate_eq_true :
    block466LeftParamsCertificate = true := by
  native_decide

theorem block466_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block466LeftL : ℝ) (block466LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block466S1 : ℝ))
    (hy2ne : y ≠ (block466S2 : ℝ))
    (hy3ne : y ≠ (block466S3 : ℝ))
    (hy4ne : y ≠ (block466S4 : ℝ)) :
    0 < block466V y := by
  have hcert := block466LeftCertificate_eq_true
  unfold block466LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block466LeftBoxes) (lo := block466LeftL) (hi := block466LeftR)
    (w1 := block466W1) (w2 := block466W2) (w3 := block466W3) (w4 := block466W4)
    (s1 := block466S1) (s2 := block466S2) (s3 := block466S3) (s4 := block466S4)
    hboxes hcover block466LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block466RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block466RightChunk000 block466W1 block466W2 block466W3 block466W4 block466S1 block466S2 block466S3 block466S4

theorem block466RightChunk000ParamsCertificate_eq_true :
    block466RightChunk000ParamsCertificate = true := by
  native_decide

theorem block466_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block466RightChunk000L : ℝ) (block466RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block466S1 : ℝ))
    (hy2ne : y ≠ (block466S2 : ℝ))
    (hy3ne : y ≠ (block466S3 : ℝ))
    (hy4ne : y ≠ (block466S4 : ℝ)) :
    0 < block466V y := by
  have hcert := block466RightChunk000Certificate_eq_true
  unfold block466RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block466RightChunk000) (lo := block466RightChunk000L) (hi := block466RightChunk000R)
    (w1 := block466W1) (w2 := block466W2) (w3 := block466W3) (w4 := block466W4)
    (s1 := block466S1) (s2 := block466S2) (s3 := block466S3) (s4 := block466S4)
    hboxes hcover block466RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block466_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block466RightL : ℝ) (block466RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block466S1 : ℝ))
    (hy2ne : y ≠ (block466S2 : ℝ))
    (hy3ne : y ≠ (block466S3 : ℝ))
    (hy4ne : y ≠ (block466S4 : ℝ)) :
    0 < block466V y := by
  have hL : (block466RightChunk000L : ℝ) = (block466RightL : ℝ) := by
    norm_num [block466RightChunk000L, block466RightL]
  have hR : (block466RightChunk000R : ℝ) = (block466RightR : ℝ) := by
    norm_num [block466RightChunk000R, block466RightR]
  have hyc : y ∈ Icc (block466RightChunk000L : ℝ) (block466RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block466_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block466_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block466LeftL : ℝ) (block466LeftR : ℝ) →
    y ≠ 0 → y ≠ (block466S1 : ℝ) → y ≠ (block466S2 : ℝ) →
    y ≠ (block466S3 : ℝ) → y ≠ (block466S4 : ℝ) → 0 < block466V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block466RightL : ℝ) (block466RightR : ℝ) →
    y ≠ 0 → y ≠ (block466S1 : ℝ) → y ≠ (block466S2 : ℝ) →
    y ≠ (block466S3 : ℝ) → y ≠ (block466S4 : ℝ) → 0 < block466V y)

theorem block466_reallog_certificate_proof :
    block466_reallog_certificate := by
  exact ⟨block466_left_V_pos, block466_right_V_pos⟩

end Block466
end M1817475
end Erdos1038Lean
