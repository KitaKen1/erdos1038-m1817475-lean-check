import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block470

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block470

open Set

def block470W1 : Rat := ((5415282002333173 : Rat) / 10000000000000000)
def block470W2 : Rat := (0 : Rat)
def block470W3 : Rat := ((1809919743565627 : Rat) / 5000000000000000)
def block470W4 : Rat := ((5135306652761577 : Rat) / 100000000000000000)
def block470S1 : Rat := ((18174751 : Rat) / 10000000)
def block470S2 : Rat := ((511587 : Rat) / 200000)
def block470S3 : Rat := ((130945476875000000123 : Rat) / 50000000000000000000)
def block470S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block470V (y : ℝ) : ℝ :=
  ratPotential block470W1 block470W2 block470W3 block470W4 block470S1 block470S2 block470S3 block470S4 y

def block470LeftParamsCertificate : Bool :=
  allBoxesSameParams block470LeftBoxes block470W1 block470W2 block470W3 block470W4 block470S1 block470S2 block470S3 block470S4

theorem block470LeftParamsCertificate_eq_true :
    block470LeftParamsCertificate = true := by
  native_decide

theorem block470_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block470LeftL : ℝ) (block470LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block470S1 : ℝ))
    (hy2ne : y ≠ (block470S2 : ℝ))
    (hy3ne : y ≠ (block470S3 : ℝ))
    (hy4ne : y ≠ (block470S4 : ℝ)) :
    0 < block470V y := by
  have hcert := block470LeftCertificate_eq_true
  unfold block470LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block470LeftBoxes) (lo := block470LeftL) (hi := block470LeftR)
    (w1 := block470W1) (w2 := block470W2) (w3 := block470W3) (w4 := block470W4)
    (s1 := block470S1) (s2 := block470S2) (s3 := block470S3) (s4 := block470S4)
    hboxes hcover block470LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block470RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block470RightChunk000 block470W1 block470W2 block470W3 block470W4 block470S1 block470S2 block470S3 block470S4

theorem block470RightChunk000ParamsCertificate_eq_true :
    block470RightChunk000ParamsCertificate = true := by
  native_decide

theorem block470_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block470RightChunk000L : ℝ) (block470RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block470S1 : ℝ))
    (hy2ne : y ≠ (block470S2 : ℝ))
    (hy3ne : y ≠ (block470S3 : ℝ))
    (hy4ne : y ≠ (block470S4 : ℝ)) :
    0 < block470V y := by
  have hcert := block470RightChunk000Certificate_eq_true
  unfold block470RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block470RightChunk000) (lo := block470RightChunk000L) (hi := block470RightChunk000R)
    (w1 := block470W1) (w2 := block470W2) (w3 := block470W3) (w4 := block470W4)
    (s1 := block470S1) (s2 := block470S2) (s3 := block470S3) (s4 := block470S4)
    hboxes hcover block470RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block470_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block470RightL : ℝ) (block470RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block470S1 : ℝ))
    (hy2ne : y ≠ (block470S2 : ℝ))
    (hy3ne : y ≠ (block470S3 : ℝ))
    (hy4ne : y ≠ (block470S4 : ℝ)) :
    0 < block470V y := by
  have hL : (block470RightChunk000L : ℝ) = (block470RightL : ℝ) := by
    norm_num [block470RightChunk000L, block470RightL]
  have hR : (block470RightChunk000R : ℝ) = (block470RightR : ℝ) := by
    norm_num [block470RightChunk000R, block470RightR]
  have hyc : y ∈ Icc (block470RightChunk000L : ℝ) (block470RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block470_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block470_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block470LeftL : ℝ) (block470LeftR : ℝ) →
    y ≠ 0 → y ≠ (block470S1 : ℝ) → y ≠ (block470S2 : ℝ) →
    y ≠ (block470S3 : ℝ) → y ≠ (block470S4 : ℝ) → 0 < block470V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block470RightL : ℝ) (block470RightR : ℝ) →
    y ≠ 0 → y ≠ (block470S1 : ℝ) → y ≠ (block470S2 : ℝ) →
    y ≠ (block470S3 : ℝ) → y ≠ (block470S4 : ℝ) → 0 < block470V y)

theorem block470_reallog_certificate_proof :
    block470_reallog_certificate := by
  exact ⟨block470_left_V_pos, block470_right_V_pos⟩

end Block470
end M1817475
end Erdos1038Lean
