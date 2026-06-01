import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block057

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block057

open Set

def block057W1 : Rat := ((3506460125493221 : Rat) / 1250000000000000)
def block057W2 : Rat := (0 : Rat)
def block057W3 : Rat := (0 : Rat)
def block057W4 : Rat := ((2628192341725981 : Rat) / 10000000000000000)
def block057S1 : Rat := ((18174751 : Rat) / 10000000)
def block057S2 : Rat := ((511587 : Rat) / 200000)
def block057S3 : Rat := ((107000619 : Rat) / 40000000)
def block057S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block057V (y : ℝ) : ℝ :=
  ratPotential block057W1 block057W2 block057W3 block057W4 block057S1 block057S2 block057S3 block057S4 y

def block057LeftParamsCertificate : Bool :=
  allBoxesSameParams block057LeftBoxes block057W1 block057W2 block057W3 block057W4 block057S1 block057S2 block057S3 block057S4

theorem block057LeftParamsCertificate_eq_true :
    block057LeftParamsCertificate = true := by
  native_decide

theorem block057_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block057LeftL : ℝ) (block057LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block057S1 : ℝ))
    (hy2ne : y ≠ (block057S2 : ℝ))
    (hy3ne : y ≠ (block057S3 : ℝ))
    (hy4ne : y ≠ (block057S4 : ℝ)) :
    0 < block057V y := by
  have hcert := block057LeftCertificate_eq_true
  unfold block057LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block057LeftBoxes) (lo := block057LeftL) (hi := block057LeftR)
    (w1 := block057W1) (w2 := block057W2) (w3 := block057W3) (w4 := block057W4)
    (s1 := block057S1) (s2 := block057S2) (s3 := block057S3) (s4 := block057S4)
    hboxes hcover block057LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block057RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block057RightChunk000 block057W1 block057W2 block057W3 block057W4 block057S1 block057S2 block057S3 block057S4

theorem block057RightChunk000ParamsCertificate_eq_true :
    block057RightChunk000ParamsCertificate = true := by
  native_decide

theorem block057_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block057RightChunk000L : ℝ) (block057RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block057S1 : ℝ))
    (hy2ne : y ≠ (block057S2 : ℝ))
    (hy3ne : y ≠ (block057S3 : ℝ))
    (hy4ne : y ≠ (block057S4 : ℝ)) :
    0 < block057V y := by
  have hcert := block057RightChunk000Certificate_eq_true
  unfold block057RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block057RightChunk000) (lo := block057RightChunk000L) (hi := block057RightChunk000R)
    (w1 := block057W1) (w2 := block057W2) (w3 := block057W3) (w4 := block057W4)
    (s1 := block057S1) (s2 := block057S2) (s3 := block057S3) (s4 := block057S4)
    hboxes hcover block057RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block057_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block057RightL : ℝ) (block057RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block057S1 : ℝ))
    (hy2ne : y ≠ (block057S2 : ℝ))
    (hy3ne : y ≠ (block057S3 : ℝ))
    (hy4ne : y ≠ (block057S4 : ℝ)) :
    0 < block057V y := by
  have hL : (block057RightChunk000L : ℝ) = (block057RightL : ℝ) := by
    norm_num [block057RightChunk000L, block057RightL]
  have hR : (block057RightChunk000R : ℝ) = (block057RightR : ℝ) := by
    norm_num [block057RightChunk000R, block057RightR]
  have hyc : y ∈ Icc (block057RightChunk000L : ℝ) (block057RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block057_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block057_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block057LeftL : ℝ) (block057LeftR : ℝ) →
    y ≠ 0 → y ≠ (block057S1 : ℝ) → y ≠ (block057S2 : ℝ) →
    y ≠ (block057S3 : ℝ) → y ≠ (block057S4 : ℝ) → 0 < block057V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block057RightL : ℝ) (block057RightR : ℝ) →
    y ≠ 0 → y ≠ (block057S1 : ℝ) → y ≠ (block057S2 : ℝ) →
    y ≠ (block057S3 : ℝ) → y ≠ (block057S4 : ℝ) → 0 < block057V y)

theorem block057_reallog_certificate_proof :
    block057_reallog_certificate := by
  exact ⟨block057_left_V_pos, block057_right_V_pos⟩

end Block057
end M1817475
end Erdos1038Lean
