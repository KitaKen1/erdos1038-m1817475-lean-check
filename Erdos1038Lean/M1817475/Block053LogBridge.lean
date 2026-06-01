import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block053

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block053

open Set

def block053W1 : Rat := ((2731102347251483 : Rat) / 1000000000000000)
def block053W2 : Rat := (0 : Rat)
def block053W3 : Rat := (0 : Rat)
def block053W4 : Rat := ((2660836937382521 : Rat) / 10000000000000000)
def block053S1 : Rat := ((18174751 : Rat) / 10000000)
def block053S2 : Rat := ((511587 : Rat) / 200000)
def block053S3 : Rat := ((107000619 : Rat) / 40000000)
def block053S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block053V (y : ℝ) : ℝ :=
  ratPotential block053W1 block053W2 block053W3 block053W4 block053S1 block053S2 block053S3 block053S4 y

def block053LeftParamsCertificate : Bool :=
  allBoxesSameParams block053LeftBoxes block053W1 block053W2 block053W3 block053W4 block053S1 block053S2 block053S3 block053S4

theorem block053LeftParamsCertificate_eq_true :
    block053LeftParamsCertificate = true := by
  native_decide

theorem block053_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block053LeftL : ℝ) (block053LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block053S1 : ℝ))
    (hy2ne : y ≠ (block053S2 : ℝ))
    (hy3ne : y ≠ (block053S3 : ℝ))
    (hy4ne : y ≠ (block053S4 : ℝ)) :
    0 < block053V y := by
  have hcert := block053LeftCertificate_eq_true
  unfold block053LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block053LeftBoxes) (lo := block053LeftL) (hi := block053LeftR)
    (w1 := block053W1) (w2 := block053W2) (w3 := block053W3) (w4 := block053W4)
    (s1 := block053S1) (s2 := block053S2) (s3 := block053S3) (s4 := block053S4)
    hboxes hcover block053LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block053RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block053RightChunk000 block053W1 block053W2 block053W3 block053W4 block053S1 block053S2 block053S3 block053S4

theorem block053RightChunk000ParamsCertificate_eq_true :
    block053RightChunk000ParamsCertificate = true := by
  native_decide

theorem block053_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block053RightChunk000L : ℝ) (block053RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block053S1 : ℝ))
    (hy2ne : y ≠ (block053S2 : ℝ))
    (hy3ne : y ≠ (block053S3 : ℝ))
    (hy4ne : y ≠ (block053S4 : ℝ)) :
    0 < block053V y := by
  have hcert := block053RightChunk000Certificate_eq_true
  unfold block053RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block053RightChunk000) (lo := block053RightChunk000L) (hi := block053RightChunk000R)
    (w1 := block053W1) (w2 := block053W2) (w3 := block053W3) (w4 := block053W4)
    (s1 := block053S1) (s2 := block053S2) (s3 := block053S3) (s4 := block053S4)
    hboxes hcover block053RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block053_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block053RightL : ℝ) (block053RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block053S1 : ℝ))
    (hy2ne : y ≠ (block053S2 : ℝ))
    (hy3ne : y ≠ (block053S3 : ℝ))
    (hy4ne : y ≠ (block053S4 : ℝ)) :
    0 < block053V y := by
  have hL : (block053RightChunk000L : ℝ) = (block053RightL : ℝ) := by
    norm_num [block053RightChunk000L, block053RightL]
  have hR : (block053RightChunk000R : ℝ) = (block053RightR : ℝ) := by
    norm_num [block053RightChunk000R, block053RightR]
  have hyc : y ∈ Icc (block053RightChunk000L : ℝ) (block053RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block053_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block053_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block053LeftL : ℝ) (block053LeftR : ℝ) →
    y ≠ 0 → y ≠ (block053S1 : ℝ) → y ≠ (block053S2 : ℝ) →
    y ≠ (block053S3 : ℝ) → y ≠ (block053S4 : ℝ) → 0 < block053V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block053RightL : ℝ) (block053RightR : ℝ) →
    y ≠ 0 → y ≠ (block053S1 : ℝ) → y ≠ (block053S2 : ℝ) →
    y ≠ (block053S3 : ℝ) → y ≠ (block053S4 : ℝ) → 0 < block053V y)

theorem block053_reallog_certificate_proof :
    block053_reallog_certificate := by
  exact ⟨block053_left_V_pos, block053_right_V_pos⟩

end Block053
end M1817475
end Erdos1038Lean
