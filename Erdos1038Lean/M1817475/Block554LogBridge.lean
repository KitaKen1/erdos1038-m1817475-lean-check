import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block554

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block554

open Set

def block554W1 : Rat := ((38386390613179383 : Rat) / 100000000000000000)
def block554W2 : Rat := (0 : Rat)
def block554W3 : Rat := ((922667916927949 : Rat) / 2000000000000000)
def block554W4 : Rat := (0 : Rat)
def block554S1 : Rat := ((18174751 : Rat) / 10000000)
def block554S2 : Rat := ((511587 : Rat) / 200000)
def block554S3 : Rat := ((25860670375000000039 : Rat) / 10000000000000000000)
def block554S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block554V (y : ℝ) : ℝ :=
  ratPotential block554W1 block554W2 block554W3 block554W4 block554S1 block554S2 block554S3 block554S4 y

def block554LeftParamsCertificate : Bool :=
  allBoxesSameParams block554LeftBoxes block554W1 block554W2 block554W3 block554W4 block554S1 block554S2 block554S3 block554S4

theorem block554LeftParamsCertificate_eq_true :
    block554LeftParamsCertificate = true := by
  native_decide

theorem block554_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block554LeftL : ℝ) (block554LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block554S1 : ℝ))
    (hy2ne : y ≠ (block554S2 : ℝ))
    (hy3ne : y ≠ (block554S3 : ℝ))
    (hy4ne : y ≠ (block554S4 : ℝ)) :
    0 < block554V y := by
  have hcert := block554LeftCertificate_eq_true
  unfold block554LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block554LeftBoxes) (lo := block554LeftL) (hi := block554LeftR)
    (w1 := block554W1) (w2 := block554W2) (w3 := block554W3) (w4 := block554W4)
    (s1 := block554S1) (s2 := block554S2) (s3 := block554S3) (s4 := block554S4)
    hboxes hcover block554LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block554RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block554RightChunk000 block554W1 block554W2 block554W3 block554W4 block554S1 block554S2 block554S3 block554S4

theorem block554RightChunk000ParamsCertificate_eq_true :
    block554RightChunk000ParamsCertificate = true := by
  native_decide

theorem block554_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block554RightChunk000L : ℝ) (block554RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block554S1 : ℝ))
    (hy2ne : y ≠ (block554S2 : ℝ))
    (hy3ne : y ≠ (block554S3 : ℝ))
    (hy4ne : y ≠ (block554S4 : ℝ)) :
    0 < block554V y := by
  have hcert := block554RightChunk000Certificate_eq_true
  unfold block554RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block554RightChunk000) (lo := block554RightChunk000L) (hi := block554RightChunk000R)
    (w1 := block554W1) (w2 := block554W2) (w3 := block554W3) (w4 := block554W4)
    (s1 := block554S1) (s2 := block554S2) (s3 := block554S3) (s4 := block554S4)
    hboxes hcover block554RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block554_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block554RightL : ℝ) (block554RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block554S1 : ℝ))
    (hy2ne : y ≠ (block554S2 : ℝ))
    (hy3ne : y ≠ (block554S3 : ℝ))
    (hy4ne : y ≠ (block554S4 : ℝ)) :
    0 < block554V y := by
  have hL : (block554RightChunk000L : ℝ) = (block554RightL : ℝ) := by
    norm_num [block554RightChunk000L, block554RightL]
  have hR : (block554RightChunk000R : ℝ) = (block554RightR : ℝ) := by
    norm_num [block554RightChunk000R, block554RightR]
  have hyc : y ∈ Icc (block554RightChunk000L : ℝ) (block554RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block554_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block554_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block554LeftL : ℝ) (block554LeftR : ℝ) →
    y ≠ 0 → y ≠ (block554S1 : ℝ) → y ≠ (block554S2 : ℝ) →
    y ≠ (block554S3 : ℝ) → y ≠ (block554S4 : ℝ) → 0 < block554V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block554RightL : ℝ) (block554RightR : ℝ) →
    y ≠ 0 → y ≠ (block554S1 : ℝ) → y ≠ (block554S2 : ℝ) →
    y ≠ (block554S3 : ℝ) → y ≠ (block554S4 : ℝ) → 0 < block554V y)

theorem block554_reallog_certificate_proof :
    block554_reallog_certificate := by
  exact ⟨block554_left_V_pos, block554_right_V_pos⟩

end Block554
end M1817475
end Erdos1038Lean
