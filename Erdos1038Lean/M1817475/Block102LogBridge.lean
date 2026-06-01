import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block102

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block102

open Set

def block102W1 : Rat := ((26074884953460593 : Rat) / 10000000000000000)
def block102W2 : Rat := (0 : Rat)
def block102W3 : Rat := ((6438819675927107 : Rat) / 125000000000000000)
def block102W4 : Rat := ((9795469950773693 : Rat) / 50000000000000000)
def block102S1 : Rat := ((18174751 : Rat) / 10000000)
def block102S2 : Rat := ((511587 : Rat) / 200000)
def block102S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block102S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block102V (y : ℝ) : ℝ :=
  ratPotential block102W1 block102W2 block102W3 block102W4 block102S1 block102S2 block102S3 block102S4 y

def block102LeftParamsCertificate : Bool :=
  allBoxesSameParams block102LeftBoxes block102W1 block102W2 block102W3 block102W4 block102S1 block102S2 block102S3 block102S4

theorem block102LeftParamsCertificate_eq_true :
    block102LeftParamsCertificate = true := by
  native_decide

theorem block102_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block102LeftL : ℝ) (block102LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block102S1 : ℝ))
    (hy2ne : y ≠ (block102S2 : ℝ))
    (hy3ne : y ≠ (block102S3 : ℝ))
    (hy4ne : y ≠ (block102S4 : ℝ)) :
    0 < block102V y := by
  have hcert := block102LeftCertificate_eq_true
  unfold block102LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block102LeftBoxes) (lo := block102LeftL) (hi := block102LeftR)
    (w1 := block102W1) (w2 := block102W2) (w3 := block102W3) (w4 := block102W4)
    (s1 := block102S1) (s2 := block102S2) (s3 := block102S3) (s4 := block102S4)
    hboxes hcover block102LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block102RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block102RightChunk000 block102W1 block102W2 block102W3 block102W4 block102S1 block102S2 block102S3 block102S4

theorem block102RightChunk000ParamsCertificate_eq_true :
    block102RightChunk000ParamsCertificate = true := by
  native_decide

theorem block102_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block102RightChunk000L : ℝ) (block102RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block102S1 : ℝ))
    (hy2ne : y ≠ (block102S2 : ℝ))
    (hy3ne : y ≠ (block102S3 : ℝ))
    (hy4ne : y ≠ (block102S4 : ℝ)) :
    0 < block102V y := by
  have hcert := block102RightChunk000Certificate_eq_true
  unfold block102RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block102RightChunk000) (lo := block102RightChunk000L) (hi := block102RightChunk000R)
    (w1 := block102W1) (w2 := block102W2) (w3 := block102W3) (w4 := block102W4)
    (s1 := block102S1) (s2 := block102S2) (s3 := block102S3) (s4 := block102S4)
    hboxes hcover block102RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block102_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block102RightL : ℝ) (block102RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block102S1 : ℝ))
    (hy2ne : y ≠ (block102S2 : ℝ))
    (hy3ne : y ≠ (block102S3 : ℝ))
    (hy4ne : y ≠ (block102S4 : ℝ)) :
    0 < block102V y := by
  have hL : (block102RightChunk000L : ℝ) = (block102RightL : ℝ) := by
    norm_num [block102RightChunk000L, block102RightL]
  have hR : (block102RightChunk000R : ℝ) = (block102RightR : ℝ) := by
    norm_num [block102RightChunk000R, block102RightR]
  have hyc : y ∈ Icc (block102RightChunk000L : ℝ) (block102RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block102_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block102_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block102LeftL : ℝ) (block102LeftR : ℝ) →
    y ≠ 0 → y ≠ (block102S1 : ℝ) → y ≠ (block102S2 : ℝ) →
    y ≠ (block102S3 : ℝ) → y ≠ (block102S4 : ℝ) → 0 < block102V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block102RightL : ℝ) (block102RightR : ℝ) →
    y ≠ 0 → y ≠ (block102S1 : ℝ) → y ≠ (block102S2 : ℝ) →
    y ≠ (block102S3 : ℝ) → y ≠ (block102S4 : ℝ) → 0 < block102V y)

theorem block102_reallog_certificate_proof :
    block102_reallog_certificate := by
  exact ⟨block102_left_V_pos, block102_right_V_pos⟩

end Block102
end M1817475
end Erdos1038Lean
