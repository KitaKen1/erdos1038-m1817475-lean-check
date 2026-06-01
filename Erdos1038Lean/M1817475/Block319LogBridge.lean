import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block319

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block319

open Set

def block319W1 : Rat := ((4720730607342863 : Rat) / 5000000000000000)
def block319W2 : Rat := ((1681965813468551 : Rat) / 25000000000000000)
def block319W3 : Rat := ((25354689154150023 : Rat) / 100000000000000000)
def block319W4 : Rat := (0 : Rat)
def block319S1 : Rat := ((18174751 : Rat) / 10000000)
def block319S2 : Rat := ((511587 : Rat) / 200000)
def block319S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block319S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block319V (y : ℝ) : ℝ :=
  ratPotential block319W1 block319W2 block319W3 block319W4 block319S1 block319S2 block319S3 block319S4 y

def block319LeftParamsCertificate : Bool :=
  allBoxesSameParams block319LeftBoxes block319W1 block319W2 block319W3 block319W4 block319S1 block319S2 block319S3 block319S4

theorem block319LeftParamsCertificate_eq_true :
    block319LeftParamsCertificate = true := by
  native_decide

theorem block319_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block319LeftL : ℝ) (block319LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block319S1 : ℝ))
    (hy2ne : y ≠ (block319S2 : ℝ))
    (hy3ne : y ≠ (block319S3 : ℝ))
    (hy4ne : y ≠ (block319S4 : ℝ)) :
    0 < block319V y := by
  have hcert := block319LeftCertificate_eq_true
  unfold block319LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block319LeftBoxes) (lo := block319LeftL) (hi := block319LeftR)
    (w1 := block319W1) (w2 := block319W2) (w3 := block319W3) (w4 := block319W4)
    (s1 := block319S1) (s2 := block319S2) (s3 := block319S3) (s4 := block319S4)
    hboxes hcover block319LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block319RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block319RightChunk000 block319W1 block319W2 block319W3 block319W4 block319S1 block319S2 block319S3 block319S4

theorem block319RightChunk000ParamsCertificate_eq_true :
    block319RightChunk000ParamsCertificate = true := by
  native_decide

theorem block319_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block319RightChunk000L : ℝ) (block319RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block319S1 : ℝ))
    (hy2ne : y ≠ (block319S2 : ℝ))
    (hy3ne : y ≠ (block319S3 : ℝ))
    (hy4ne : y ≠ (block319S4 : ℝ)) :
    0 < block319V y := by
  have hcert := block319RightChunk000Certificate_eq_true
  unfold block319RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block319RightChunk000) (lo := block319RightChunk000L) (hi := block319RightChunk000R)
    (w1 := block319W1) (w2 := block319W2) (w3 := block319W3) (w4 := block319W4)
    (s1 := block319S1) (s2 := block319S2) (s3 := block319S3) (s4 := block319S4)
    hboxes hcover block319RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block319_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block319RightL : ℝ) (block319RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block319S1 : ℝ))
    (hy2ne : y ≠ (block319S2 : ℝ))
    (hy3ne : y ≠ (block319S3 : ℝ))
    (hy4ne : y ≠ (block319S4 : ℝ)) :
    0 < block319V y := by
  have hL : (block319RightChunk000L : ℝ) = (block319RightL : ℝ) := by
    norm_num [block319RightChunk000L, block319RightL]
  have hR : (block319RightChunk000R : ℝ) = (block319RightR : ℝ) := by
    norm_num [block319RightChunk000R, block319RightR]
  have hyc : y ∈ Icc (block319RightChunk000L : ℝ) (block319RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block319_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block319_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block319LeftL : ℝ) (block319LeftR : ℝ) →
    y ≠ 0 → y ≠ (block319S1 : ℝ) → y ≠ (block319S2 : ℝ) →
    y ≠ (block319S3 : ℝ) → y ≠ (block319S4 : ℝ) → 0 < block319V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block319RightL : ℝ) (block319RightR : ℝ) →
    y ≠ 0 → y ≠ (block319S1 : ℝ) → y ≠ (block319S2 : ℝ) →
    y ≠ (block319S3 : ℝ) → y ≠ (block319S4 : ℝ) → 0 < block319V y)

theorem block319_reallog_certificate_proof :
    block319_reallog_certificate := by
  exact ⟨block319_left_V_pos, block319_right_V_pos⟩

end Block319
end M1817475
end Erdos1038Lean
