import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block440

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block440

open Set

def block440W1 : Rat := ((6263230733922749 : Rat) / 10000000000000000)
def block440W2 : Rat := (0 : Rat)
def block440W3 : Rat := ((16007180896167447 : Rat) / 50000000000000000)
def block440W4 : Rat := ((3687511510628841 : Rat) / 50000000000000000)
def block440S1 : Rat := ((18174751 : Rat) / 10000000)
def block440S2 : Rat := ((511587 : Rat) / 200000)
def block440S3 : Rat := ((131531950089285714383 : Rat) / 50000000000000000000)
def block440S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block440V (y : ℝ) : ℝ :=
  ratPotential block440W1 block440W2 block440W3 block440W4 block440S1 block440S2 block440S3 block440S4 y

def block440LeftParamsCertificate : Bool :=
  allBoxesSameParams block440LeftBoxes block440W1 block440W2 block440W3 block440W4 block440S1 block440S2 block440S3 block440S4

theorem block440LeftParamsCertificate_eq_true :
    block440LeftParamsCertificate = true := by
  native_decide

theorem block440_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block440LeftL : ℝ) (block440LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block440S1 : ℝ))
    (hy2ne : y ≠ (block440S2 : ℝ))
    (hy3ne : y ≠ (block440S3 : ℝ))
    (hy4ne : y ≠ (block440S4 : ℝ)) :
    0 < block440V y := by
  have hcert := block440LeftCertificate_eq_true
  unfold block440LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block440LeftBoxes) (lo := block440LeftL) (hi := block440LeftR)
    (w1 := block440W1) (w2 := block440W2) (w3 := block440W3) (w4 := block440W4)
    (s1 := block440S1) (s2 := block440S2) (s3 := block440S3) (s4 := block440S4)
    hboxes hcover block440LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block440RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block440RightChunk000 block440W1 block440W2 block440W3 block440W4 block440S1 block440S2 block440S3 block440S4

theorem block440RightChunk000ParamsCertificate_eq_true :
    block440RightChunk000ParamsCertificate = true := by
  native_decide

theorem block440_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block440RightChunk000L : ℝ) (block440RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block440S1 : ℝ))
    (hy2ne : y ≠ (block440S2 : ℝ))
    (hy3ne : y ≠ (block440S3 : ℝ))
    (hy4ne : y ≠ (block440S4 : ℝ)) :
    0 < block440V y := by
  have hcert := block440RightChunk000Certificate_eq_true
  unfold block440RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block440RightChunk000) (lo := block440RightChunk000L) (hi := block440RightChunk000R)
    (w1 := block440W1) (w2 := block440W2) (w3 := block440W3) (w4 := block440W4)
    (s1 := block440S1) (s2 := block440S2) (s3 := block440S3) (s4 := block440S4)
    hboxes hcover block440RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block440_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block440RightL : ℝ) (block440RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block440S1 : ℝ))
    (hy2ne : y ≠ (block440S2 : ℝ))
    (hy3ne : y ≠ (block440S3 : ℝ))
    (hy4ne : y ≠ (block440S4 : ℝ)) :
    0 < block440V y := by
  have hL : (block440RightChunk000L : ℝ) = (block440RightL : ℝ) := by
    norm_num [block440RightChunk000L, block440RightL]
  have hR : (block440RightChunk000R : ℝ) = (block440RightR : ℝ) := by
    norm_num [block440RightChunk000R, block440RightR]
  have hyc : y ∈ Icc (block440RightChunk000L : ℝ) (block440RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block440_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block440_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block440LeftL : ℝ) (block440LeftR : ℝ) →
    y ≠ 0 → y ≠ (block440S1 : ℝ) → y ≠ (block440S2 : ℝ) →
    y ≠ (block440S3 : ℝ) → y ≠ (block440S4 : ℝ) → 0 < block440V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block440RightL : ℝ) (block440RightR : ℝ) →
    y ≠ 0 → y ≠ (block440S1 : ℝ) → y ≠ (block440S2 : ℝ) →
    y ≠ (block440S3 : ℝ) → y ≠ (block440S4 : ℝ) → 0 < block440V y)

theorem block440_reallog_certificate_proof :
    block440_reallog_certificate := by
  exact ⟨block440_left_V_pos, block440_right_V_pos⟩

end Block440
end M1817475
end Erdos1038Lean
