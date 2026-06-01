import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block045

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block045

open Set

def block045W1 : Rat := ((1621459334108481 : Rat) / 625000000000000)
def block045W2 : Rat := (0 : Rat)
def block045W3 : Rat := (0 : Rat)
def block045W4 : Rat := ((5447009682447549 : Rat) / 20000000000000000)
def block045S1 : Rat := ((18174751 : Rat) / 10000000)
def block045S2 : Rat := ((511587 : Rat) / 200000)
def block045S3 : Rat := ((107000619 : Rat) / 40000000)
def block045S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block045V (y : ℝ) : ℝ :=
  ratPotential block045W1 block045W2 block045W3 block045W4 block045S1 block045S2 block045S3 block045S4 y

def block045LeftParamsCertificate : Bool :=
  allBoxesSameParams block045LeftBoxes block045W1 block045W2 block045W3 block045W4 block045S1 block045S2 block045S3 block045S4

theorem block045LeftParamsCertificate_eq_true :
    block045LeftParamsCertificate = true := by
  native_decide

theorem block045_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block045LeftL : ℝ) (block045LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block045S1 : ℝ))
    (hy2ne : y ≠ (block045S2 : ℝ))
    (hy3ne : y ≠ (block045S3 : ℝ))
    (hy4ne : y ≠ (block045S4 : ℝ)) :
    0 < block045V y := by
  have hcert := block045LeftCertificate_eq_true
  unfold block045LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block045LeftBoxes) (lo := block045LeftL) (hi := block045LeftR)
    (w1 := block045W1) (w2 := block045W2) (w3 := block045W3) (w4 := block045W4)
    (s1 := block045S1) (s2 := block045S2) (s3 := block045S3) (s4 := block045S4)
    hboxes hcover block045LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block045RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block045RightChunk000 block045W1 block045W2 block045W3 block045W4 block045S1 block045S2 block045S3 block045S4

theorem block045RightChunk000ParamsCertificate_eq_true :
    block045RightChunk000ParamsCertificate = true := by
  native_decide

theorem block045_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block045RightChunk000L : ℝ) (block045RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block045S1 : ℝ))
    (hy2ne : y ≠ (block045S2 : ℝ))
    (hy3ne : y ≠ (block045S3 : ℝ))
    (hy4ne : y ≠ (block045S4 : ℝ)) :
    0 < block045V y := by
  have hcert := block045RightChunk000Certificate_eq_true
  unfold block045RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block045RightChunk000) (lo := block045RightChunk000L) (hi := block045RightChunk000R)
    (w1 := block045W1) (w2 := block045W2) (w3 := block045W3) (w4 := block045W4)
    (s1 := block045S1) (s2 := block045S2) (s3 := block045S3) (s4 := block045S4)
    hboxes hcover block045RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block045_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block045RightL : ℝ) (block045RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block045S1 : ℝ))
    (hy2ne : y ≠ (block045S2 : ℝ))
    (hy3ne : y ≠ (block045S3 : ℝ))
    (hy4ne : y ≠ (block045S4 : ℝ)) :
    0 < block045V y := by
  have hL : (block045RightChunk000L : ℝ) = (block045RightL : ℝ) := by
    norm_num [block045RightChunk000L, block045RightL]
  have hR : (block045RightChunk000R : ℝ) = (block045RightR : ℝ) := by
    norm_num [block045RightChunk000R, block045RightR]
  have hyc : y ∈ Icc (block045RightChunk000L : ℝ) (block045RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block045_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block045_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block045LeftL : ℝ) (block045LeftR : ℝ) →
    y ≠ 0 → y ≠ (block045S1 : ℝ) → y ≠ (block045S2 : ℝ) →
    y ≠ (block045S3 : ℝ) → y ≠ (block045S4 : ℝ) → 0 < block045V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block045RightL : ℝ) (block045RightR : ℝ) →
    y ≠ 0 → y ≠ (block045S1 : ℝ) → y ≠ (block045S2 : ℝ) →
    y ≠ (block045S3 : ℝ) → y ≠ (block045S4 : ℝ) → 0 < block045V y)

theorem block045_reallog_certificate_proof :
    block045_reallog_certificate := by
  exact ⟨block045_left_V_pos, block045_right_V_pos⟩

end Block045
end M1817475
end Erdos1038Lean
