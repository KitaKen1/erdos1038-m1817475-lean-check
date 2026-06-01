import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block096

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block096

open Set

def block096W1 : Rat := ((424023315958443 : Rat) / 200000000000000)
def block096W2 : Rat := (0 : Rat)
def block096W3 : Rat := ((350950255184761 : Rat) / 5000000000000000)
def block096W4 : Rat := ((4868142456372647 : Rat) / 25000000000000000)
def block096S1 : Rat := ((18174751 : Rat) / 10000000)
def block096S2 : Rat := ((511587 : Rat) / 200000)
def block096S3 : Rat := ((135304927767857142789 : Rat) / 50000000000000000000)
def block096S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block096V (y : ℝ) : ℝ :=
  ratPotential block096W1 block096W2 block096W3 block096W4 block096S1 block096S2 block096S3 block096S4 y

def block096LeftParamsCertificate : Bool :=
  allBoxesSameParams block096LeftBoxes block096W1 block096W2 block096W3 block096W4 block096S1 block096S2 block096S3 block096S4

theorem block096LeftParamsCertificate_eq_true :
    block096LeftParamsCertificate = true := by
  native_decide

theorem block096_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block096LeftL : ℝ) (block096LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block096S1 : ℝ))
    (hy2ne : y ≠ (block096S2 : ℝ))
    (hy3ne : y ≠ (block096S3 : ℝ))
    (hy4ne : y ≠ (block096S4 : ℝ)) :
    0 < block096V y := by
  have hcert := block096LeftCertificate_eq_true
  unfold block096LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block096LeftBoxes) (lo := block096LeftL) (hi := block096LeftR)
    (w1 := block096W1) (w2 := block096W2) (w3 := block096W3) (w4 := block096W4)
    (s1 := block096S1) (s2 := block096S2) (s3 := block096S3) (s4 := block096S4)
    hboxes hcover block096LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block096RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block096RightChunk000 block096W1 block096W2 block096W3 block096W4 block096S1 block096S2 block096S3 block096S4

theorem block096RightChunk000ParamsCertificate_eq_true :
    block096RightChunk000ParamsCertificate = true := by
  native_decide

theorem block096_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block096RightChunk000L : ℝ) (block096RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block096S1 : ℝ))
    (hy2ne : y ≠ (block096S2 : ℝ))
    (hy3ne : y ≠ (block096S3 : ℝ))
    (hy4ne : y ≠ (block096S4 : ℝ)) :
    0 < block096V y := by
  have hcert := block096RightChunk000Certificate_eq_true
  unfold block096RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block096RightChunk000) (lo := block096RightChunk000L) (hi := block096RightChunk000R)
    (w1 := block096W1) (w2 := block096W2) (w3 := block096W3) (w4 := block096W4)
    (s1 := block096S1) (s2 := block096S2) (s3 := block096S3) (s4 := block096S4)
    hboxes hcover block096RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block096_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block096RightL : ℝ) (block096RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block096S1 : ℝ))
    (hy2ne : y ≠ (block096S2 : ℝ))
    (hy3ne : y ≠ (block096S3 : ℝ))
    (hy4ne : y ≠ (block096S4 : ℝ)) :
    0 < block096V y := by
  have hL : (block096RightChunk000L : ℝ) = (block096RightL : ℝ) := by
    norm_num [block096RightChunk000L, block096RightL]
  have hR : (block096RightChunk000R : ℝ) = (block096RightR : ℝ) := by
    norm_num [block096RightChunk000R, block096RightR]
  have hyc : y ∈ Icc (block096RightChunk000L : ℝ) (block096RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block096_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block096_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block096LeftL : ℝ) (block096LeftR : ℝ) →
    y ≠ 0 → y ≠ (block096S1 : ℝ) → y ≠ (block096S2 : ℝ) →
    y ≠ (block096S3 : ℝ) → y ≠ (block096S4 : ℝ) → 0 < block096V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block096RightL : ℝ) (block096RightR : ℝ) →
    y ≠ 0 → y ≠ (block096S1 : ℝ) → y ≠ (block096S2 : ℝ) →
    y ≠ (block096S3 : ℝ) → y ≠ (block096S4 : ℝ) → 0 < block096V y)

theorem block096_reallog_certificate_proof :
    block096_reallog_certificate := by
  exact ⟨block096_left_V_pos, block096_right_V_pos⟩

end Block096
end M1817475
end Erdos1038Lean
