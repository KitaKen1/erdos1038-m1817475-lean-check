import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block325

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block325

open Set

def block325W1 : Rat := ((4801301767797357 : Rat) / 5000000000000000)
def block325W2 : Rat := ((23266081636169257 : Rat) / 500000000000000000)
def block325W3 : Rat := ((14255829249693697 : Rat) / 100000000000000000)
def block325W4 : Rat := ((1366466809614847 : Rat) / 10000000000000000)
def block325S1 : Rat := ((18174751 : Rat) / 10000000)
def block325S2 : Rat := ((511587 : Rat) / 200000)
def block325S3 : Rat := ((107000619 : Rat) / 40000000)
def block325S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block325V (y : ℝ) : ℝ :=
  ratPotential block325W1 block325W2 block325W3 block325W4 block325S1 block325S2 block325S3 block325S4 y

def block325LeftParamsCertificate : Bool :=
  allBoxesSameParams block325LeftBoxes block325W1 block325W2 block325W3 block325W4 block325S1 block325S2 block325S3 block325S4

theorem block325LeftParamsCertificate_eq_true :
    block325LeftParamsCertificate = true := by
  native_decide

theorem block325_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block325LeftL : ℝ) (block325LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block325S1 : ℝ))
    (hy2ne : y ≠ (block325S2 : ℝ))
    (hy3ne : y ≠ (block325S3 : ℝ))
    (hy4ne : y ≠ (block325S4 : ℝ)) :
    0 < block325V y := by
  have hcert := block325LeftCertificate_eq_true
  unfold block325LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block325LeftBoxes) (lo := block325LeftL) (hi := block325LeftR)
    (w1 := block325W1) (w2 := block325W2) (w3 := block325W3) (w4 := block325W4)
    (s1 := block325S1) (s2 := block325S2) (s3 := block325S3) (s4 := block325S4)
    hboxes hcover block325LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block325RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block325RightChunk000 block325W1 block325W2 block325W3 block325W4 block325S1 block325S2 block325S3 block325S4

theorem block325RightChunk000ParamsCertificate_eq_true :
    block325RightChunk000ParamsCertificate = true := by
  native_decide

theorem block325_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block325RightChunk000L : ℝ) (block325RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block325S1 : ℝ))
    (hy2ne : y ≠ (block325S2 : ℝ))
    (hy3ne : y ≠ (block325S3 : ℝ))
    (hy4ne : y ≠ (block325S4 : ℝ)) :
    0 < block325V y := by
  have hcert := block325RightChunk000Certificate_eq_true
  unfold block325RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block325RightChunk000) (lo := block325RightChunk000L) (hi := block325RightChunk000R)
    (w1 := block325W1) (w2 := block325W2) (w3 := block325W3) (w4 := block325W4)
    (s1 := block325S1) (s2 := block325S2) (s3 := block325S3) (s4 := block325S4)
    hboxes hcover block325RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block325_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block325RightL : ℝ) (block325RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block325S1 : ℝ))
    (hy2ne : y ≠ (block325S2 : ℝ))
    (hy3ne : y ≠ (block325S3 : ℝ))
    (hy4ne : y ≠ (block325S4 : ℝ)) :
    0 < block325V y := by
  have hL : (block325RightChunk000L : ℝ) = (block325RightL : ℝ) := by
    norm_num [block325RightChunk000L, block325RightL]
  have hR : (block325RightChunk000R : ℝ) = (block325RightR : ℝ) := by
    norm_num [block325RightChunk000R, block325RightR]
  have hyc : y ∈ Icc (block325RightChunk000L : ℝ) (block325RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block325_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block325_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block325LeftL : ℝ) (block325LeftR : ℝ) →
    y ≠ 0 → y ≠ (block325S1 : ℝ) → y ≠ (block325S2 : ℝ) →
    y ≠ (block325S3 : ℝ) → y ≠ (block325S4 : ℝ) → 0 < block325V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block325RightL : ℝ) (block325RightR : ℝ) →
    y ≠ 0 → y ≠ (block325S1 : ℝ) → y ≠ (block325S2 : ℝ) →
    y ≠ (block325S3 : ℝ) → y ≠ (block325S4 : ℝ) → 0 < block325V y)

theorem block325_reallog_certificate_proof :
    block325_reallog_certificate := by
  exact ⟨block325_left_V_pos, block325_right_V_pos⟩

end Block325
end M1817475
end Erdos1038Lean
