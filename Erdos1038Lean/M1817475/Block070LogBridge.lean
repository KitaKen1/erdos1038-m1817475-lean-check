import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block070

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block070

open Set

def block070W1 : Rat := ((30773538779252463 : Rat) / 10000000000000000)
def block070W2 : Rat := (0 : Rat)
def block070W3 : Rat := (0 : Rat)
def block070W4 : Rat := ((1257568491294751 : Rat) / 5000000000000000)
def block070S1 : Rat := ((18174751 : Rat) / 10000000)
def block070S2 : Rat := ((511587 : Rat) / 200000)
def block070S3 : Rat := ((107000619 : Rat) / 40000000)
def block070S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block070V (y : ℝ) : ℝ :=
  ratPotential block070W1 block070W2 block070W3 block070W4 block070S1 block070S2 block070S3 block070S4 y

def block070LeftParamsCertificate : Bool :=
  allBoxesSameParams block070LeftBoxes block070W1 block070W2 block070W3 block070W4 block070S1 block070S2 block070S3 block070S4

theorem block070LeftParamsCertificate_eq_true :
    block070LeftParamsCertificate = true := by
  native_decide

theorem block070_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block070LeftL : ℝ) (block070LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block070S1 : ℝ))
    (hy2ne : y ≠ (block070S2 : ℝ))
    (hy3ne : y ≠ (block070S3 : ℝ))
    (hy4ne : y ≠ (block070S4 : ℝ)) :
    0 < block070V y := by
  have hcert := block070LeftCertificate_eq_true
  unfold block070LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block070LeftBoxes) (lo := block070LeftL) (hi := block070LeftR)
    (w1 := block070W1) (w2 := block070W2) (w3 := block070W3) (w4 := block070W4)
    (s1 := block070S1) (s2 := block070S2) (s3 := block070S3) (s4 := block070S4)
    hboxes hcover block070LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block070RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block070RightChunk000 block070W1 block070W2 block070W3 block070W4 block070S1 block070S2 block070S3 block070S4

theorem block070RightChunk000ParamsCertificate_eq_true :
    block070RightChunk000ParamsCertificate = true := by
  native_decide

theorem block070_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block070RightChunk000L : ℝ) (block070RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block070S1 : ℝ))
    (hy2ne : y ≠ (block070S2 : ℝ))
    (hy3ne : y ≠ (block070S3 : ℝ))
    (hy4ne : y ≠ (block070S4 : ℝ)) :
    0 < block070V y := by
  have hcert := block070RightChunk000Certificate_eq_true
  unfold block070RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block070RightChunk000) (lo := block070RightChunk000L) (hi := block070RightChunk000R)
    (w1 := block070W1) (w2 := block070W2) (w3 := block070W3) (w4 := block070W4)
    (s1 := block070S1) (s2 := block070S2) (s3 := block070S3) (s4 := block070S4)
    hboxes hcover block070RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block070_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block070RightL : ℝ) (block070RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block070S1 : ℝ))
    (hy2ne : y ≠ (block070S2 : ℝ))
    (hy3ne : y ≠ (block070S3 : ℝ))
    (hy4ne : y ≠ (block070S4 : ℝ)) :
    0 < block070V y := by
  have hL : (block070RightChunk000L : ℝ) = (block070RightL : ℝ) := by
    norm_num [block070RightChunk000L, block070RightL]
  have hR : (block070RightChunk000R : ℝ) = (block070RightR : ℝ) := by
    norm_num [block070RightChunk000R, block070RightR]
  have hyc : y ∈ Icc (block070RightChunk000L : ℝ) (block070RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block070_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block070_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block070LeftL : ℝ) (block070LeftR : ℝ) →
    y ≠ 0 → y ≠ (block070S1 : ℝ) → y ≠ (block070S2 : ℝ) →
    y ≠ (block070S3 : ℝ) → y ≠ (block070S4 : ℝ) → 0 < block070V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block070RightL : ℝ) (block070RightR : ℝ) →
    y ≠ 0 → y ≠ (block070S1 : ℝ) → y ≠ (block070S2 : ℝ) →
    y ≠ (block070S3 : ℝ) → y ≠ (block070S4 : ℝ) → 0 < block070V y)

theorem block070_reallog_certificate_proof :
    block070_reallog_certificate := by
  exact ⟨block070_left_V_pos, block070_right_V_pos⟩

end Block070
end M1817475
end Erdos1038Lean
