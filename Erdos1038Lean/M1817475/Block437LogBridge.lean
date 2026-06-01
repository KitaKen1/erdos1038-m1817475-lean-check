import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block437

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block437

open Set

def block437W1 : Rat := ((6353152316524899 : Rat) / 10000000000000000)
def block437W2 : Rat := (0 : Rat)
def block437W3 : Rat := ((3163218035687889 : Rat) / 10000000000000000)
def block437W4 : Rat := ((7568401681001853 : Rat) / 100000000000000000)
def block437S1 : Rat := ((18174751 : Rat) / 10000000)
def block437S2 : Rat := ((511587 : Rat) / 200000)
def block437S3 : Rat := ((131590597410714285809 : Rat) / 50000000000000000000)
def block437S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block437V (y : ℝ) : ℝ :=
  ratPotential block437W1 block437W2 block437W3 block437W4 block437S1 block437S2 block437S3 block437S4 y

def block437LeftParamsCertificate : Bool :=
  allBoxesSameParams block437LeftBoxes block437W1 block437W2 block437W3 block437W4 block437S1 block437S2 block437S3 block437S4

theorem block437LeftParamsCertificate_eq_true :
    block437LeftParamsCertificate = true := by
  native_decide

theorem block437_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block437LeftL : ℝ) (block437LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block437S1 : ℝ))
    (hy2ne : y ≠ (block437S2 : ℝ))
    (hy3ne : y ≠ (block437S3 : ℝ))
    (hy4ne : y ≠ (block437S4 : ℝ)) :
    0 < block437V y := by
  have hcert := block437LeftCertificate_eq_true
  unfold block437LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block437LeftBoxes) (lo := block437LeftL) (hi := block437LeftR)
    (w1 := block437W1) (w2 := block437W2) (w3 := block437W3) (w4 := block437W4)
    (s1 := block437S1) (s2 := block437S2) (s3 := block437S3) (s4 := block437S4)
    hboxes hcover block437LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block437RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block437RightChunk000 block437W1 block437W2 block437W3 block437W4 block437S1 block437S2 block437S3 block437S4

theorem block437RightChunk000ParamsCertificate_eq_true :
    block437RightChunk000ParamsCertificate = true := by
  native_decide

theorem block437_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block437RightChunk000L : ℝ) (block437RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block437S1 : ℝ))
    (hy2ne : y ≠ (block437S2 : ℝ))
    (hy3ne : y ≠ (block437S3 : ℝ))
    (hy4ne : y ≠ (block437S4 : ℝ)) :
    0 < block437V y := by
  have hcert := block437RightChunk000Certificate_eq_true
  unfold block437RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block437RightChunk000) (lo := block437RightChunk000L) (hi := block437RightChunk000R)
    (w1 := block437W1) (w2 := block437W2) (w3 := block437W3) (w4 := block437W4)
    (s1 := block437S1) (s2 := block437S2) (s3 := block437S3) (s4 := block437S4)
    hboxes hcover block437RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block437_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block437RightL : ℝ) (block437RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block437S1 : ℝ))
    (hy2ne : y ≠ (block437S2 : ℝ))
    (hy3ne : y ≠ (block437S3 : ℝ))
    (hy4ne : y ≠ (block437S4 : ℝ)) :
    0 < block437V y := by
  have hL : (block437RightChunk000L : ℝ) = (block437RightL : ℝ) := by
    norm_num [block437RightChunk000L, block437RightL]
  have hR : (block437RightChunk000R : ℝ) = (block437RightR : ℝ) := by
    norm_num [block437RightChunk000R, block437RightR]
  have hyc : y ∈ Icc (block437RightChunk000L : ℝ) (block437RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block437_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block437_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block437LeftL : ℝ) (block437LeftR : ℝ) →
    y ≠ 0 → y ≠ (block437S1 : ℝ) → y ≠ (block437S2 : ℝ) →
    y ≠ (block437S3 : ℝ) → y ≠ (block437S4 : ℝ) → 0 < block437V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block437RightL : ℝ) (block437RightR : ℝ) →
    y ≠ 0 → y ≠ (block437S1 : ℝ) → y ≠ (block437S2 : ℝ) →
    y ≠ (block437S3 : ℝ) → y ≠ (block437S4 : ℝ) → 0 < block437V y)

theorem block437_reallog_certificate_proof :
    block437_reallog_certificate := by
  exact ⟨block437_left_V_pos, block437_right_V_pos⟩

end Block437
end M1817475
end Erdos1038Lean
