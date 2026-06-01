import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block381

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block381

open Set

def block381W1 : Rat := ((4239372031116001 : Rat) / 5000000000000000)
def block381W2 : Rat := ((581564592121991 : Rat) / 12500000000000000)
def block381W3 : Rat := ((3959504638655089 : Rat) / 25000000000000000)
def block381W4 : Rat := ((2810125566573189 : Rat) / 20000000000000000)
def block381S1 : Rat := ((18174751 : Rat) / 10000000)
def block381S2 : Rat := ((511587 : Rat) / 200000)
def block381S3 : Rat := ((132685347410714285761 : Rat) / 50000000000000000000)
def block381S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block381V (y : ℝ) : ℝ :=
  ratPotential block381W1 block381W2 block381W3 block381W4 block381S1 block381S2 block381S3 block381S4 y

def block381LeftParamsCertificate : Bool :=
  allBoxesSameParams block381LeftBoxes block381W1 block381W2 block381W3 block381W4 block381S1 block381S2 block381S3 block381S4

theorem block381LeftParamsCertificate_eq_true :
    block381LeftParamsCertificate = true := by
  native_decide

theorem block381_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block381LeftL : ℝ) (block381LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block381S1 : ℝ))
    (hy2ne : y ≠ (block381S2 : ℝ))
    (hy3ne : y ≠ (block381S3 : ℝ))
    (hy4ne : y ≠ (block381S4 : ℝ)) :
    0 < block381V y := by
  have hcert := block381LeftCertificate_eq_true
  unfold block381LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block381LeftBoxes) (lo := block381LeftL) (hi := block381LeftR)
    (w1 := block381W1) (w2 := block381W2) (w3 := block381W3) (w4 := block381W4)
    (s1 := block381S1) (s2 := block381S2) (s3 := block381S3) (s4 := block381S4)
    hboxes hcover block381LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block381RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block381RightChunk000 block381W1 block381W2 block381W3 block381W4 block381S1 block381S2 block381S3 block381S4

theorem block381RightChunk000ParamsCertificate_eq_true :
    block381RightChunk000ParamsCertificate = true := by
  native_decide

theorem block381_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block381RightChunk000L : ℝ) (block381RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block381S1 : ℝ))
    (hy2ne : y ≠ (block381S2 : ℝ))
    (hy3ne : y ≠ (block381S3 : ℝ))
    (hy4ne : y ≠ (block381S4 : ℝ)) :
    0 < block381V y := by
  have hcert := block381RightChunk000Certificate_eq_true
  unfold block381RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block381RightChunk000) (lo := block381RightChunk000L) (hi := block381RightChunk000R)
    (w1 := block381W1) (w2 := block381W2) (w3 := block381W3) (w4 := block381W4)
    (s1 := block381S1) (s2 := block381S2) (s3 := block381S3) (s4 := block381S4)
    hboxes hcover block381RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block381_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block381RightL : ℝ) (block381RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block381S1 : ℝ))
    (hy2ne : y ≠ (block381S2 : ℝ))
    (hy3ne : y ≠ (block381S3 : ℝ))
    (hy4ne : y ≠ (block381S4 : ℝ)) :
    0 < block381V y := by
  have hL : (block381RightChunk000L : ℝ) = (block381RightL : ℝ) := by
    norm_num [block381RightChunk000L, block381RightL]
  have hR : (block381RightChunk000R : ℝ) = (block381RightR : ℝ) := by
    norm_num [block381RightChunk000R, block381RightR]
  have hyc : y ∈ Icc (block381RightChunk000L : ℝ) (block381RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block381_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block381_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block381LeftL : ℝ) (block381LeftR : ℝ) →
    y ≠ 0 → y ≠ (block381S1 : ℝ) → y ≠ (block381S2 : ℝ) →
    y ≠ (block381S3 : ℝ) → y ≠ (block381S4 : ℝ) → 0 < block381V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block381RightL : ℝ) (block381RightR : ℝ) →
    y ≠ 0 → y ≠ (block381S1 : ℝ) → y ≠ (block381S2 : ℝ) →
    y ≠ (block381S3 : ℝ) → y ≠ (block381S4 : ℝ) → 0 < block381V y)

theorem block381_reallog_certificate_proof :
    block381_reallog_certificate := by
  exact ⟨block381_left_V_pos, block381_right_V_pos⟩

end Block381
end M1817475
end Erdos1038Lean
