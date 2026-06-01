import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block147

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block147

open Set

def block147W1 : Rat := ((572116772986757 : Rat) / 250000000000000)
def block147W2 : Rat := (0 : Rat)
def block147W3 : Rat := ((952771186421973 : Rat) / 6250000000000000)
def block147W4 : Rat := ((4744730661638503 : Rat) / 50000000000000000)
def block147S1 : Rat := ((18174751 : Rat) / 10000000)
def block147S2 : Rat := ((511587 : Rat) / 200000)
def block147S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block147S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block147V (y : ℝ) : ℝ :=
  ratPotential block147W1 block147W2 block147W3 block147W4 block147S1 block147S2 block147S3 block147S4 y

def block147LeftParamsCertificate : Bool :=
  allBoxesSameParams block147LeftBoxes block147W1 block147W2 block147W3 block147W4 block147S1 block147S2 block147S3 block147S4

theorem block147LeftParamsCertificate_eq_true :
    block147LeftParamsCertificate = true := by
  native_decide

theorem block147_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block147LeftL : ℝ) (block147LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block147S1 : ℝ))
    (hy2ne : y ≠ (block147S2 : ℝ))
    (hy3ne : y ≠ (block147S3 : ℝ))
    (hy4ne : y ≠ (block147S4 : ℝ)) :
    0 < block147V y := by
  have hcert := block147LeftCertificate_eq_true
  unfold block147LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block147LeftBoxes) (lo := block147LeftL) (hi := block147LeftR)
    (w1 := block147W1) (w2 := block147W2) (w3 := block147W3) (w4 := block147W4)
    (s1 := block147S1) (s2 := block147S2) (s3 := block147S3) (s4 := block147S4)
    hboxes hcover block147LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block147RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block147RightChunk000 block147W1 block147W2 block147W3 block147W4 block147S1 block147S2 block147S3 block147S4

theorem block147RightChunk000ParamsCertificate_eq_true :
    block147RightChunk000ParamsCertificate = true := by
  native_decide

theorem block147_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block147RightChunk000L : ℝ) (block147RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block147S1 : ℝ))
    (hy2ne : y ≠ (block147S2 : ℝ))
    (hy3ne : y ≠ (block147S3 : ℝ))
    (hy4ne : y ≠ (block147S4 : ℝ)) :
    0 < block147V y := by
  have hcert := block147RightChunk000Certificate_eq_true
  unfold block147RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block147RightChunk000) (lo := block147RightChunk000L) (hi := block147RightChunk000R)
    (w1 := block147W1) (w2 := block147W2) (w3 := block147W3) (w4 := block147W4)
    (s1 := block147S1) (s2 := block147S2) (s3 := block147S3) (s4 := block147S4)
    hboxes hcover block147RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block147_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block147RightL : ℝ) (block147RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block147S1 : ℝ))
    (hy2ne : y ≠ (block147S2 : ℝ))
    (hy3ne : y ≠ (block147S3 : ℝ))
    (hy4ne : y ≠ (block147S4 : ℝ)) :
    0 < block147V y := by
  have hL : (block147RightChunk000L : ℝ) = (block147RightL : ℝ) := by
    norm_num [block147RightChunk000L, block147RightL]
  have hR : (block147RightChunk000R : ℝ) = (block147RightR : ℝ) := by
    norm_num [block147RightChunk000R, block147RightR]
  have hyc : y ∈ Icc (block147RightChunk000L : ℝ) (block147RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block147_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block147_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block147LeftL : ℝ) (block147LeftR : ℝ) →
    y ≠ 0 → y ≠ (block147S1 : ℝ) → y ≠ (block147S2 : ℝ) →
    y ≠ (block147S3 : ℝ) → y ≠ (block147S4 : ℝ) → 0 < block147V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block147RightL : ℝ) (block147RightR : ℝ) →
    y ≠ 0 → y ≠ (block147S1 : ℝ) → y ≠ (block147S2 : ℝ) →
    y ≠ (block147S3 : ℝ) → y ≠ (block147S4 : ℝ) → 0 < block147V y)

theorem block147_reallog_certificate_proof :
    block147_reallog_certificate := by
  exact ⟨block147_left_V_pos, block147_right_V_pos⟩

end Block147
end M1817475
end Erdos1038Lean
