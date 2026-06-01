import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block441

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block441

open Set

def block441W1 : Rat := ((6235468728195461 : Rat) / 10000000000000000)
def block441W2 : Rat := (0 : Rat)
def block441W3 : Rat := ((32127870380805257 : Rat) / 100000000000000000)
def block441W4 : Rat := ((3660355940938359 : Rat) / 50000000000000000)
def block441S1 : Rat := ((18174751 : Rat) / 10000000)
def block441S2 : Rat := ((511587 : Rat) / 200000)
def block441S3 : Rat := ((131512400982142857241 : Rat) / 50000000000000000000)
def block441S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block441V (y : ℝ) : ℝ :=
  ratPotential block441W1 block441W2 block441W3 block441W4 block441S1 block441S2 block441S3 block441S4 y

def block441LeftParamsCertificate : Bool :=
  allBoxesSameParams block441LeftBoxes block441W1 block441W2 block441W3 block441W4 block441S1 block441S2 block441S3 block441S4

theorem block441LeftParamsCertificate_eq_true :
    block441LeftParamsCertificate = true := by
  native_decide

theorem block441_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block441LeftL : ℝ) (block441LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block441S1 : ℝ))
    (hy2ne : y ≠ (block441S2 : ℝ))
    (hy3ne : y ≠ (block441S3 : ℝ))
    (hy4ne : y ≠ (block441S4 : ℝ)) :
    0 < block441V y := by
  have hcert := block441LeftCertificate_eq_true
  unfold block441LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block441LeftBoxes) (lo := block441LeftL) (hi := block441LeftR)
    (w1 := block441W1) (w2 := block441W2) (w3 := block441W3) (w4 := block441W4)
    (s1 := block441S1) (s2 := block441S2) (s3 := block441S3) (s4 := block441S4)
    hboxes hcover block441LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block441RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block441RightChunk000 block441W1 block441W2 block441W3 block441W4 block441S1 block441S2 block441S3 block441S4

theorem block441RightChunk000ParamsCertificate_eq_true :
    block441RightChunk000ParamsCertificate = true := by
  native_decide

theorem block441_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block441RightChunk000L : ℝ) (block441RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block441S1 : ℝ))
    (hy2ne : y ≠ (block441S2 : ℝ))
    (hy3ne : y ≠ (block441S3 : ℝ))
    (hy4ne : y ≠ (block441S4 : ℝ)) :
    0 < block441V y := by
  have hcert := block441RightChunk000Certificate_eq_true
  unfold block441RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block441RightChunk000) (lo := block441RightChunk000L) (hi := block441RightChunk000R)
    (w1 := block441W1) (w2 := block441W2) (w3 := block441W3) (w4 := block441W4)
    (s1 := block441S1) (s2 := block441S2) (s3 := block441S3) (s4 := block441S4)
    hboxes hcover block441RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block441_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block441RightL : ℝ) (block441RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block441S1 : ℝ))
    (hy2ne : y ≠ (block441S2 : ℝ))
    (hy3ne : y ≠ (block441S3 : ℝ))
    (hy4ne : y ≠ (block441S4 : ℝ)) :
    0 < block441V y := by
  have hL : (block441RightChunk000L : ℝ) = (block441RightL : ℝ) := by
    norm_num [block441RightChunk000L, block441RightL]
  have hR : (block441RightChunk000R : ℝ) = (block441RightR : ℝ) := by
    norm_num [block441RightChunk000R, block441RightR]
  have hyc : y ∈ Icc (block441RightChunk000L : ℝ) (block441RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block441_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block441_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block441LeftL : ℝ) (block441LeftR : ℝ) →
    y ≠ 0 → y ≠ (block441S1 : ℝ) → y ≠ (block441S2 : ℝ) →
    y ≠ (block441S3 : ℝ) → y ≠ (block441S4 : ℝ) → 0 < block441V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block441RightL : ℝ) (block441RightR : ℝ) →
    y ≠ 0 → y ≠ (block441S1 : ℝ) → y ≠ (block441S2 : ℝ) →
    y ≠ (block441S3 : ℝ) → y ≠ (block441S4 : ℝ) → 0 < block441V y)

theorem block441_reallog_certificate_proof :
    block441_reallog_certificate := by
  exact ⟨block441_left_V_pos, block441_right_V_pos⟩

end Block441
end M1817475
end Erdos1038Lean
