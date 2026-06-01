import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block090

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block090

open Set

def block090W1 : Rat := ((1812116489393827 : Rat) / 500000000000000)
def block090W2 : Rat := (0 : Rat)
def block090W3 : Rat := (0 : Rat)
def block090W4 : Rat := ((23147706678328803 : Rat) / 100000000000000000)
def block090S1 : Rat := ((18174751 : Rat) / 10000000)
def block090S2 : Rat := ((511587 : Rat) / 200000)
def block090S3 : Rat := ((107000619 : Rat) / 40000000)
def block090S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block090V (y : ℝ) : ℝ :=
  ratPotential block090W1 block090W2 block090W3 block090W4 block090S1 block090S2 block090S3 block090S4 y

def block090LeftParamsCertificate : Bool :=
  allBoxesSameParams block090LeftBoxes block090W1 block090W2 block090W3 block090W4 block090S1 block090S2 block090S3 block090S4

theorem block090LeftParamsCertificate_eq_true :
    block090LeftParamsCertificate = true := by
  native_decide

theorem block090_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block090LeftL : ℝ) (block090LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block090S1 : ℝ))
    (hy2ne : y ≠ (block090S2 : ℝ))
    (hy3ne : y ≠ (block090S3 : ℝ))
    (hy4ne : y ≠ (block090S4 : ℝ)) :
    0 < block090V y := by
  have hcert := block090LeftCertificate_eq_true
  unfold block090LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block090LeftBoxes) (lo := block090LeftL) (hi := block090LeftR)
    (w1 := block090W1) (w2 := block090W2) (w3 := block090W3) (w4 := block090W4)
    (s1 := block090S1) (s2 := block090S2) (s3 := block090S3) (s4 := block090S4)
    hboxes hcover block090LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block090RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block090RightChunk000 block090W1 block090W2 block090W3 block090W4 block090S1 block090S2 block090S3 block090S4

theorem block090RightChunk000ParamsCertificate_eq_true :
    block090RightChunk000ParamsCertificate = true := by
  native_decide

theorem block090_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block090RightChunk000L : ℝ) (block090RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block090S1 : ℝ))
    (hy2ne : y ≠ (block090S2 : ℝ))
    (hy3ne : y ≠ (block090S3 : ℝ))
    (hy4ne : y ≠ (block090S4 : ℝ)) :
    0 < block090V y := by
  have hcert := block090RightChunk000Certificate_eq_true
  unfold block090RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block090RightChunk000) (lo := block090RightChunk000L) (hi := block090RightChunk000R)
    (w1 := block090W1) (w2 := block090W2) (w3 := block090W3) (w4 := block090W4)
    (s1 := block090S1) (s2 := block090S2) (s3 := block090S3) (s4 := block090S4)
    hboxes hcover block090RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block090_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block090RightL : ℝ) (block090RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block090S1 : ℝ))
    (hy2ne : y ≠ (block090S2 : ℝ))
    (hy3ne : y ≠ (block090S3 : ℝ))
    (hy4ne : y ≠ (block090S4 : ℝ)) :
    0 < block090V y := by
  have hL : (block090RightChunk000L : ℝ) = (block090RightL : ℝ) := by
    norm_num [block090RightChunk000L, block090RightL]
  have hR : (block090RightChunk000R : ℝ) = (block090RightR : ℝ) := by
    norm_num [block090RightChunk000R, block090RightR]
  have hyc : y ∈ Icc (block090RightChunk000L : ℝ) (block090RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block090_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block090_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block090LeftL : ℝ) (block090LeftR : ℝ) →
    y ≠ 0 → y ≠ (block090S1 : ℝ) → y ≠ (block090S2 : ℝ) →
    y ≠ (block090S3 : ℝ) → y ≠ (block090S4 : ℝ) → 0 < block090V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block090RightL : ℝ) (block090RightR : ℝ) →
    y ≠ 0 → y ≠ (block090S1 : ℝ) → y ≠ (block090S2 : ℝ) →
    y ≠ (block090S3 : ℝ) → y ≠ (block090S4 : ℝ) → 0 < block090V y)

theorem block090_reallog_certificate_proof :
    block090_reallog_certificate := by
  exact ⟨block090_left_V_pos, block090_right_V_pos⟩

end Block090
end M1817475
end Erdos1038Lean
