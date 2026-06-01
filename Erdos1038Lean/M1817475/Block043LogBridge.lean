import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block043

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block043

open Set

def block043W1 : Rat := ((1281145463926003 : Rat) / 500000000000000)
def block043W2 : Rat := (0 : Rat)
def block043W3 : Rat := (0 : Rat)
def block043W4 : Rat := ((684666283719807 : Rat) / 2500000000000000)
def block043S1 : Rat := ((18174751 : Rat) / 10000000)
def block043S2 : Rat := ((511587 : Rat) / 200000)
def block043S3 : Rat := ((107000619 : Rat) / 40000000)
def block043S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block043V (y : ℝ) : ℝ :=
  ratPotential block043W1 block043W2 block043W3 block043W4 block043S1 block043S2 block043S3 block043S4 y

def block043LeftParamsCertificate : Bool :=
  allBoxesSameParams block043LeftBoxes block043W1 block043W2 block043W3 block043W4 block043S1 block043S2 block043S3 block043S4

theorem block043LeftParamsCertificate_eq_true :
    block043LeftParamsCertificate = true := by
  native_decide

theorem block043_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block043LeftL : ℝ) (block043LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block043S1 : ℝ))
    (hy2ne : y ≠ (block043S2 : ℝ))
    (hy3ne : y ≠ (block043S3 : ℝ))
    (hy4ne : y ≠ (block043S4 : ℝ)) :
    0 < block043V y := by
  have hcert := block043LeftCertificate_eq_true
  unfold block043LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block043LeftBoxes) (lo := block043LeftL) (hi := block043LeftR)
    (w1 := block043W1) (w2 := block043W2) (w3 := block043W3) (w4 := block043W4)
    (s1 := block043S1) (s2 := block043S2) (s3 := block043S3) (s4 := block043S4)
    hboxes hcover block043LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block043RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block043RightChunk000 block043W1 block043W2 block043W3 block043W4 block043S1 block043S2 block043S3 block043S4

theorem block043RightChunk000ParamsCertificate_eq_true :
    block043RightChunk000ParamsCertificate = true := by
  native_decide

theorem block043_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block043RightChunk000L : ℝ) (block043RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block043S1 : ℝ))
    (hy2ne : y ≠ (block043S2 : ℝ))
    (hy3ne : y ≠ (block043S3 : ℝ))
    (hy4ne : y ≠ (block043S4 : ℝ)) :
    0 < block043V y := by
  have hcert := block043RightChunk000Certificate_eq_true
  unfold block043RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block043RightChunk000) (lo := block043RightChunk000L) (hi := block043RightChunk000R)
    (w1 := block043W1) (w2 := block043W2) (w3 := block043W3) (w4 := block043W4)
    (s1 := block043S1) (s2 := block043S2) (s3 := block043S3) (s4 := block043S4)
    hboxes hcover block043RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block043_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block043RightL : ℝ) (block043RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block043S1 : ℝ))
    (hy2ne : y ≠ (block043S2 : ℝ))
    (hy3ne : y ≠ (block043S3 : ℝ))
    (hy4ne : y ≠ (block043S4 : ℝ)) :
    0 < block043V y := by
  have hL : (block043RightChunk000L : ℝ) = (block043RightL : ℝ) := by
    norm_num [block043RightChunk000L, block043RightL]
  have hR : (block043RightChunk000R : ℝ) = (block043RightR : ℝ) := by
    norm_num [block043RightChunk000R, block043RightR]
  have hyc : y ∈ Icc (block043RightChunk000L : ℝ) (block043RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block043_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block043_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block043LeftL : ℝ) (block043LeftR : ℝ) →
    y ≠ 0 → y ≠ (block043S1 : ℝ) → y ≠ (block043S2 : ℝ) →
    y ≠ (block043S3 : ℝ) → y ≠ (block043S4 : ℝ) → 0 < block043V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block043RightL : ℝ) (block043RightR : ℝ) →
    y ≠ 0 → y ≠ (block043S1 : ℝ) → y ≠ (block043S2 : ℝ) →
    y ≠ (block043S3 : ℝ) → y ≠ (block043S4 : ℝ) → 0 < block043V y)

theorem block043_reallog_certificate_proof :
    block043_reallog_certificate := by
  exact ⟨block043_left_V_pos, block043_right_V_pos⟩

end Block043
end M1817475
end Erdos1038Lean
