import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block464

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block464

open Set

def block464W1 : Rat := ((2791278961038837 : Rat) / 5000000000000000)
def block464W2 : Rat := (0 : Rat)
def block464W3 : Rat := ((35263574451737983 : Rat) / 100000000000000000)
def block464W4 : Rat := ((28309625699240143 : Rat) / 500000000000000000)
def block464S1 : Rat := ((18174751 : Rat) / 10000000)
def block464S2 : Rat := ((511587 : Rat) / 200000)
def block464S3 : Rat := ((5242510860714285719 : Rat) / 2000000000000000000)
def block464S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block464V (y : ℝ) : ℝ :=
  ratPotential block464W1 block464W2 block464W3 block464W4 block464S1 block464S2 block464S3 block464S4 y

def block464LeftParamsCertificate : Bool :=
  allBoxesSameParams block464LeftBoxes block464W1 block464W2 block464W3 block464W4 block464S1 block464S2 block464S3 block464S4

theorem block464LeftParamsCertificate_eq_true :
    block464LeftParamsCertificate = true := by
  native_decide

theorem block464_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block464LeftL : ℝ) (block464LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block464S1 : ℝ))
    (hy2ne : y ≠ (block464S2 : ℝ))
    (hy3ne : y ≠ (block464S3 : ℝ))
    (hy4ne : y ≠ (block464S4 : ℝ)) :
    0 < block464V y := by
  have hcert := block464LeftCertificate_eq_true
  unfold block464LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block464LeftBoxes) (lo := block464LeftL) (hi := block464LeftR)
    (w1 := block464W1) (w2 := block464W2) (w3 := block464W3) (w4 := block464W4)
    (s1 := block464S1) (s2 := block464S2) (s3 := block464S3) (s4 := block464S4)
    hboxes hcover block464LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block464RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block464RightChunk000 block464W1 block464W2 block464W3 block464W4 block464S1 block464S2 block464S3 block464S4

theorem block464RightChunk000ParamsCertificate_eq_true :
    block464RightChunk000ParamsCertificate = true := by
  native_decide

theorem block464_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block464RightChunk000L : ℝ) (block464RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block464S1 : ℝ))
    (hy2ne : y ≠ (block464S2 : ℝ))
    (hy3ne : y ≠ (block464S3 : ℝ))
    (hy4ne : y ≠ (block464S4 : ℝ)) :
    0 < block464V y := by
  have hcert := block464RightChunk000Certificate_eq_true
  unfold block464RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block464RightChunk000) (lo := block464RightChunk000L) (hi := block464RightChunk000R)
    (w1 := block464W1) (w2 := block464W2) (w3 := block464W3) (w4 := block464W4)
    (s1 := block464S1) (s2 := block464S2) (s3 := block464S3) (s4 := block464S4)
    hboxes hcover block464RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block464_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block464RightL : ℝ) (block464RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block464S1 : ℝ))
    (hy2ne : y ≠ (block464S2 : ℝ))
    (hy3ne : y ≠ (block464S3 : ℝ))
    (hy4ne : y ≠ (block464S4 : ℝ)) :
    0 < block464V y := by
  have hL : (block464RightChunk000L : ℝ) = (block464RightL : ℝ) := by
    norm_num [block464RightChunk000L, block464RightL]
  have hR : (block464RightChunk000R : ℝ) = (block464RightR : ℝ) := by
    norm_num [block464RightChunk000R, block464RightR]
  have hyc : y ∈ Icc (block464RightChunk000L : ℝ) (block464RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block464_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block464_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block464LeftL : ℝ) (block464LeftR : ℝ) →
    y ≠ 0 → y ≠ (block464S1 : ℝ) → y ≠ (block464S2 : ℝ) →
    y ≠ (block464S3 : ℝ) → y ≠ (block464S4 : ℝ) → 0 < block464V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block464RightL : ℝ) (block464RightR : ℝ) →
    y ≠ 0 → y ≠ (block464S1 : ℝ) → y ≠ (block464S2 : ℝ) →
    y ≠ (block464S3 : ℝ) → y ≠ (block464S4 : ℝ) → 0 < block464V y)

theorem block464_reallog_certificate_proof :
    block464_reallog_certificate := by
  exact ⟨block464_left_V_pos, block464_right_V_pos⟩

end Block464
end M1817475
end Erdos1038Lean
