import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block036

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block036

open Set

def block036W1 : Rat := ((2456176637055803 : Rat) / 1000000000000000)
def block036W2 : Rat := (0 : Rat)
def block036W3 : Rat := (0 : Rat)
def block036W4 : Rat := ((348782888199863 : Rat) / 1250000000000000)
def block036S1 : Rat := ((18174751 : Rat) / 10000000)
def block036S2 : Rat := ((511587 : Rat) / 200000)
def block036S3 : Rat := ((107000619 : Rat) / 40000000)
def block036S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block036V (y : ℝ) : ℝ :=
  ratPotential block036W1 block036W2 block036W3 block036W4 block036S1 block036S2 block036S3 block036S4 y

def block036LeftParamsCertificate : Bool :=
  allBoxesSameParams block036LeftBoxes block036W1 block036W2 block036W3 block036W4 block036S1 block036S2 block036S3 block036S4

theorem block036LeftParamsCertificate_eq_true :
    block036LeftParamsCertificate = true := by
  native_decide

theorem block036_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block036LeftL : ℝ) (block036LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block036S1 : ℝ))
    (hy2ne : y ≠ (block036S2 : ℝ))
    (hy3ne : y ≠ (block036S3 : ℝ))
    (hy4ne : y ≠ (block036S4 : ℝ)) :
    0 < block036V y := by
  have hcert := block036LeftCertificate_eq_true
  unfold block036LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block036LeftBoxes) (lo := block036LeftL) (hi := block036LeftR)
    (w1 := block036W1) (w2 := block036W2) (w3 := block036W3) (w4 := block036W4)
    (s1 := block036S1) (s2 := block036S2) (s3 := block036S3) (s4 := block036S4)
    hboxes hcover block036LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block036RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block036RightChunk000 block036W1 block036W2 block036W3 block036W4 block036S1 block036S2 block036S3 block036S4

theorem block036RightChunk000ParamsCertificate_eq_true :
    block036RightChunk000ParamsCertificate = true := by
  native_decide

theorem block036_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block036RightChunk000L : ℝ) (block036RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block036S1 : ℝ))
    (hy2ne : y ≠ (block036S2 : ℝ))
    (hy3ne : y ≠ (block036S3 : ℝ))
    (hy4ne : y ≠ (block036S4 : ℝ)) :
    0 < block036V y := by
  have hcert := block036RightChunk000Certificate_eq_true
  unfold block036RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block036RightChunk000) (lo := block036RightChunk000L) (hi := block036RightChunk000R)
    (w1 := block036W1) (w2 := block036W2) (w3 := block036W3) (w4 := block036W4)
    (s1 := block036S1) (s2 := block036S2) (s3 := block036S3) (s4 := block036S4)
    hboxes hcover block036RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block036_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block036RightL : ℝ) (block036RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block036S1 : ℝ))
    (hy2ne : y ≠ (block036S2 : ℝ))
    (hy3ne : y ≠ (block036S3 : ℝ))
    (hy4ne : y ≠ (block036S4 : ℝ)) :
    0 < block036V y := by
  have hL : (block036RightChunk000L : ℝ) = (block036RightL : ℝ) := by
    norm_num [block036RightChunk000L, block036RightL]
  have hR : (block036RightChunk000R : ℝ) = (block036RightR : ℝ) := by
    norm_num [block036RightChunk000R, block036RightR]
  have hyc : y ∈ Icc (block036RightChunk000L : ℝ) (block036RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block036_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block036_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block036LeftL : ℝ) (block036LeftR : ℝ) →
    y ≠ 0 → y ≠ (block036S1 : ℝ) → y ≠ (block036S2 : ℝ) →
    y ≠ (block036S3 : ℝ) → y ≠ (block036S4 : ℝ) → 0 < block036V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block036RightL : ℝ) (block036RightR : ℝ) →
    y ≠ 0 → y ≠ (block036S1 : ℝ) → y ≠ (block036S2 : ℝ) →
    y ≠ (block036S3 : ℝ) → y ≠ (block036S4 : ℝ) → 0 < block036V y)

theorem block036_reallog_certificate_proof :
    block036_reallog_certificate := by
  exact ⟨block036_left_V_pos, block036_right_V_pos⟩

end Block036
end M1817475
end Erdos1038Lean
