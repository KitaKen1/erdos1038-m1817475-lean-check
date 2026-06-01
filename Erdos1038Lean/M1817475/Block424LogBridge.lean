import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block424

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block424

open Set

def block424W1 : Rat := ((3372226353034497 : Rat) / 5000000000000000)
def block424W2 : Rat := (0 : Rat)
def block424W3 : Rat := ((150578293661611 : Rat) / 500000000000000)
def block424W4 : Rat := ((8295852755252991 : Rat) / 100000000000000000)
def block424S1 : Rat := ((18174751 : Rat) / 10000000)
def block424S2 : Rat := ((511587 : Rat) / 200000)
def block424S3 : Rat := ((26368947160714285731 : Rat) / 10000000000000000000)
def block424S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block424V (y : ℝ) : ℝ :=
  ratPotential block424W1 block424W2 block424W3 block424W4 block424S1 block424S2 block424S3 block424S4 y

def block424LeftParamsCertificate : Bool :=
  allBoxesSameParams block424LeftBoxes block424W1 block424W2 block424W3 block424W4 block424S1 block424S2 block424S3 block424S4

theorem block424LeftParamsCertificate_eq_true :
    block424LeftParamsCertificate = true := by
  native_decide

theorem block424_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block424LeftL : ℝ) (block424LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block424S1 : ℝ))
    (hy2ne : y ≠ (block424S2 : ℝ))
    (hy3ne : y ≠ (block424S3 : ℝ))
    (hy4ne : y ≠ (block424S4 : ℝ)) :
    0 < block424V y := by
  have hcert := block424LeftCertificate_eq_true
  unfold block424LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block424LeftBoxes) (lo := block424LeftL) (hi := block424LeftR)
    (w1 := block424W1) (w2 := block424W2) (w3 := block424W3) (w4 := block424W4)
    (s1 := block424S1) (s2 := block424S2) (s3 := block424S3) (s4 := block424S4)
    hboxes hcover block424LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block424RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block424RightChunk000 block424W1 block424W2 block424W3 block424W4 block424S1 block424S2 block424S3 block424S4

theorem block424RightChunk000ParamsCertificate_eq_true :
    block424RightChunk000ParamsCertificate = true := by
  native_decide

theorem block424_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block424RightChunk000L : ℝ) (block424RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block424S1 : ℝ))
    (hy2ne : y ≠ (block424S2 : ℝ))
    (hy3ne : y ≠ (block424S3 : ℝ))
    (hy4ne : y ≠ (block424S4 : ℝ)) :
    0 < block424V y := by
  have hcert := block424RightChunk000Certificate_eq_true
  unfold block424RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block424RightChunk000) (lo := block424RightChunk000L) (hi := block424RightChunk000R)
    (w1 := block424W1) (w2 := block424W2) (w3 := block424W3) (w4 := block424W4)
    (s1 := block424S1) (s2 := block424S2) (s3 := block424S3) (s4 := block424S4)
    hboxes hcover block424RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block424_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block424RightL : ℝ) (block424RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block424S1 : ℝ))
    (hy2ne : y ≠ (block424S2 : ℝ))
    (hy3ne : y ≠ (block424S3 : ℝ))
    (hy4ne : y ≠ (block424S4 : ℝ)) :
    0 < block424V y := by
  have hL : (block424RightChunk000L : ℝ) = (block424RightL : ℝ) := by
    norm_num [block424RightChunk000L, block424RightL]
  have hR : (block424RightChunk000R : ℝ) = (block424RightR : ℝ) := by
    norm_num [block424RightChunk000R, block424RightR]
  have hyc : y ∈ Icc (block424RightChunk000L : ℝ) (block424RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block424_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block424_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block424LeftL : ℝ) (block424LeftR : ℝ) →
    y ≠ 0 → y ≠ (block424S1 : ℝ) → y ≠ (block424S2 : ℝ) →
    y ≠ (block424S3 : ℝ) → y ≠ (block424S4 : ℝ) → 0 < block424V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block424RightL : ℝ) (block424RightR : ℝ) →
    y ≠ 0 → y ≠ (block424S1 : ℝ) → y ≠ (block424S2 : ℝ) →
    y ≠ (block424S3 : ℝ) → y ≠ (block424S4 : ℝ) → 0 < block424V y)

theorem block424_reallog_certificate_proof :
    block424_reallog_certificate := by
  exact ⟨block424_left_V_pos, block424_right_V_pos⟩

end Block424
end M1817475
end Erdos1038Lean
