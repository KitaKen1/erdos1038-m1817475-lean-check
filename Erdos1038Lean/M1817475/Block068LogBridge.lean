import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block068

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block068

open Set

def block068W1 : Rat := ((7579922240830509 : Rat) / 2500000000000000)
def block068W2 : Rat := (0 : Rat)
def block068W3 : Rat := (0 : Rat)
def block068W4 : Rat := ((1266643632770569 : Rat) / 5000000000000000)
def block068S1 : Rat := ((18174751 : Rat) / 10000000)
def block068S2 : Rat := ((511587 : Rat) / 200000)
def block068S3 : Rat := ((107000619 : Rat) / 40000000)
def block068S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block068V (y : ℝ) : ℝ :=
  ratPotential block068W1 block068W2 block068W3 block068W4 block068S1 block068S2 block068S3 block068S4 y

def block068LeftParamsCertificate : Bool :=
  allBoxesSameParams block068LeftBoxes block068W1 block068W2 block068W3 block068W4 block068S1 block068S2 block068S3 block068S4

theorem block068LeftParamsCertificate_eq_true :
    block068LeftParamsCertificate = true := by
  native_decide

theorem block068_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block068LeftL : ℝ) (block068LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block068S1 : ℝ))
    (hy2ne : y ≠ (block068S2 : ℝ))
    (hy3ne : y ≠ (block068S3 : ℝ))
    (hy4ne : y ≠ (block068S4 : ℝ)) :
    0 < block068V y := by
  have hcert := block068LeftCertificate_eq_true
  unfold block068LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block068LeftBoxes) (lo := block068LeftL) (hi := block068LeftR)
    (w1 := block068W1) (w2 := block068W2) (w3 := block068W3) (w4 := block068W4)
    (s1 := block068S1) (s2 := block068S2) (s3 := block068S3) (s4 := block068S4)
    hboxes hcover block068LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block068RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block068RightChunk000 block068W1 block068W2 block068W3 block068W4 block068S1 block068S2 block068S3 block068S4

theorem block068RightChunk000ParamsCertificate_eq_true :
    block068RightChunk000ParamsCertificate = true := by
  native_decide

theorem block068_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block068RightChunk000L : ℝ) (block068RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block068S1 : ℝ))
    (hy2ne : y ≠ (block068S2 : ℝ))
    (hy3ne : y ≠ (block068S3 : ℝ))
    (hy4ne : y ≠ (block068S4 : ℝ)) :
    0 < block068V y := by
  have hcert := block068RightChunk000Certificate_eq_true
  unfold block068RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block068RightChunk000) (lo := block068RightChunk000L) (hi := block068RightChunk000R)
    (w1 := block068W1) (w2 := block068W2) (w3 := block068W3) (w4 := block068W4)
    (s1 := block068S1) (s2 := block068S2) (s3 := block068S3) (s4 := block068S4)
    hboxes hcover block068RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block068_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block068RightL : ℝ) (block068RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block068S1 : ℝ))
    (hy2ne : y ≠ (block068S2 : ℝ))
    (hy3ne : y ≠ (block068S3 : ℝ))
    (hy4ne : y ≠ (block068S4 : ℝ)) :
    0 < block068V y := by
  have hL : (block068RightChunk000L : ℝ) = (block068RightL : ℝ) := by
    norm_num [block068RightChunk000L, block068RightL]
  have hR : (block068RightChunk000R : ℝ) = (block068RightR : ℝ) := by
    norm_num [block068RightChunk000R, block068RightR]
  have hyc : y ∈ Icc (block068RightChunk000L : ℝ) (block068RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block068_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block068_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block068LeftL : ℝ) (block068LeftR : ℝ) →
    y ≠ 0 → y ≠ (block068S1 : ℝ) → y ≠ (block068S2 : ℝ) →
    y ≠ (block068S3 : ℝ) → y ≠ (block068S4 : ℝ) → 0 < block068V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block068RightL : ℝ) (block068RightR : ℝ) →
    y ≠ 0 → y ≠ (block068S1 : ℝ) → y ≠ (block068S2 : ℝ) →
    y ≠ (block068S3 : ℝ) → y ≠ (block068S4 : ℝ) → 0 < block068V y)

theorem block068_reallog_certificate_proof :
    block068_reallog_certificate := by
  exact ⟨block068_left_V_pos, block068_right_V_pos⟩

end Block068
end M1817475
end Erdos1038Lean
