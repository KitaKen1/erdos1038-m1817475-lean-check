import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block049

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block049

open Set

def block049W1 : Rat := ((2660929313504537 : Rat) / 1000000000000000)
def block049W2 : Rat := (0 : Rat)
def block049W3 : Rat := (0 : Rat)
def block049W4 : Rat := ((6731472729794069 : Rat) / 25000000000000000)
def block049S1 : Rat := ((18174751 : Rat) / 10000000)
def block049S2 : Rat := ((511587 : Rat) / 200000)
def block049S3 : Rat := ((107000619 : Rat) / 40000000)
def block049S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block049V (y : ℝ) : ℝ :=
  ratPotential block049W1 block049W2 block049W3 block049W4 block049S1 block049S2 block049S3 block049S4 y

def block049LeftParamsCertificate : Bool :=
  allBoxesSameParams block049LeftBoxes block049W1 block049W2 block049W3 block049W4 block049S1 block049S2 block049S3 block049S4

theorem block049LeftParamsCertificate_eq_true :
    block049LeftParamsCertificate = true := by
  native_decide

theorem block049_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block049LeftL : ℝ) (block049LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block049S1 : ℝ))
    (hy2ne : y ≠ (block049S2 : ℝ))
    (hy3ne : y ≠ (block049S3 : ℝ))
    (hy4ne : y ≠ (block049S4 : ℝ)) :
    0 < block049V y := by
  have hcert := block049LeftCertificate_eq_true
  unfold block049LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block049LeftBoxes) (lo := block049LeftL) (hi := block049LeftR)
    (w1 := block049W1) (w2 := block049W2) (w3 := block049W3) (w4 := block049W4)
    (s1 := block049S1) (s2 := block049S2) (s3 := block049S3) (s4 := block049S4)
    hboxes hcover block049LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block049RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block049RightChunk000 block049W1 block049W2 block049W3 block049W4 block049S1 block049S2 block049S3 block049S4

theorem block049RightChunk000ParamsCertificate_eq_true :
    block049RightChunk000ParamsCertificate = true := by
  native_decide

theorem block049_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block049RightChunk000L : ℝ) (block049RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block049S1 : ℝ))
    (hy2ne : y ≠ (block049S2 : ℝ))
    (hy3ne : y ≠ (block049S3 : ℝ))
    (hy4ne : y ≠ (block049S4 : ℝ)) :
    0 < block049V y := by
  have hcert := block049RightChunk000Certificate_eq_true
  unfold block049RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block049RightChunk000) (lo := block049RightChunk000L) (hi := block049RightChunk000R)
    (w1 := block049W1) (w2 := block049W2) (w3 := block049W3) (w4 := block049W4)
    (s1 := block049S1) (s2 := block049S2) (s3 := block049S3) (s4 := block049S4)
    hboxes hcover block049RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block049_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block049RightL : ℝ) (block049RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block049S1 : ℝ))
    (hy2ne : y ≠ (block049S2 : ℝ))
    (hy3ne : y ≠ (block049S3 : ℝ))
    (hy4ne : y ≠ (block049S4 : ℝ)) :
    0 < block049V y := by
  have hL : (block049RightChunk000L : ℝ) = (block049RightL : ℝ) := by
    norm_num [block049RightChunk000L, block049RightL]
  have hR : (block049RightChunk000R : ℝ) = (block049RightR : ℝ) := by
    norm_num [block049RightChunk000R, block049RightR]
  have hyc : y ∈ Icc (block049RightChunk000L : ℝ) (block049RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block049_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block049_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block049LeftL : ℝ) (block049LeftR : ℝ) →
    y ≠ 0 → y ≠ (block049S1 : ℝ) → y ≠ (block049S2 : ℝ) →
    y ≠ (block049S3 : ℝ) → y ≠ (block049S4 : ℝ) → 0 < block049V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block049RightL : ℝ) (block049RightR : ℝ) →
    y ≠ 0 → y ≠ (block049S1 : ℝ) → y ≠ (block049S2 : ℝ) →
    y ≠ (block049S3 : ℝ) → y ≠ (block049S4 : ℝ) → 0 < block049V y)

theorem block049_reallog_certificate_proof :
    block049_reallog_certificate := by
  exact ⟨block049_left_V_pos, block049_right_V_pos⟩

end Block049
end M1817475
end Erdos1038Lean
