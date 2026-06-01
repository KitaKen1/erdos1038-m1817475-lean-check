import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block453

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block453

open Set

def block453W1 : Rat := ((5889850115436757 : Rat) / 10000000000000000)
def block453W2 : Rat := (0 : Rat)
def block453W3 : Rat := ((1685070269429751 : Rat) / 5000000000000000)
def block453W4 : Rat := ((3253310595528649 : Rat) / 50000000000000000)
def block453S1 : Rat := ((18174751 : Rat) / 10000000)
def block453S2 : Rat := ((511587 : Rat) / 200000)
def block453S3 : Rat := ((131277811696428571537 : Rat) / 50000000000000000000)
def block453S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block453V (y : ℝ) : ℝ :=
  ratPotential block453W1 block453W2 block453W3 block453W4 block453S1 block453S2 block453S3 block453S4 y

def block453LeftParamsCertificate : Bool :=
  allBoxesSameParams block453LeftBoxes block453W1 block453W2 block453W3 block453W4 block453S1 block453S2 block453S3 block453S4

theorem block453LeftParamsCertificate_eq_true :
    block453LeftParamsCertificate = true := by
  native_decide

theorem block453_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block453LeftL : ℝ) (block453LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block453S1 : ℝ))
    (hy2ne : y ≠ (block453S2 : ℝ))
    (hy3ne : y ≠ (block453S3 : ℝ))
    (hy4ne : y ≠ (block453S4 : ℝ)) :
    0 < block453V y := by
  have hcert := block453LeftCertificate_eq_true
  unfold block453LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block453LeftBoxes) (lo := block453LeftL) (hi := block453LeftR)
    (w1 := block453W1) (w2 := block453W2) (w3 := block453W3) (w4 := block453W4)
    (s1 := block453S1) (s2 := block453S2) (s3 := block453S3) (s4 := block453S4)
    hboxes hcover block453LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block453RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block453RightChunk000 block453W1 block453W2 block453W3 block453W4 block453S1 block453S2 block453S3 block453S4

theorem block453RightChunk000ParamsCertificate_eq_true :
    block453RightChunk000ParamsCertificate = true := by
  native_decide

theorem block453_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block453RightChunk000L : ℝ) (block453RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block453S1 : ℝ))
    (hy2ne : y ≠ (block453S2 : ℝ))
    (hy3ne : y ≠ (block453S3 : ℝ))
    (hy4ne : y ≠ (block453S4 : ℝ)) :
    0 < block453V y := by
  have hcert := block453RightChunk000Certificate_eq_true
  unfold block453RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block453RightChunk000) (lo := block453RightChunk000L) (hi := block453RightChunk000R)
    (w1 := block453W1) (w2 := block453W2) (w3 := block453W3) (w4 := block453W4)
    (s1 := block453S1) (s2 := block453S2) (s3 := block453S3) (s4 := block453S4)
    hboxes hcover block453RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block453_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block453RightL : ℝ) (block453RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block453S1 : ℝ))
    (hy2ne : y ≠ (block453S2 : ℝ))
    (hy3ne : y ≠ (block453S3 : ℝ))
    (hy4ne : y ≠ (block453S4 : ℝ)) :
    0 < block453V y := by
  have hL : (block453RightChunk000L : ℝ) = (block453RightL : ℝ) := by
    norm_num [block453RightChunk000L, block453RightL]
  have hR : (block453RightChunk000R : ℝ) = (block453RightR : ℝ) := by
    norm_num [block453RightChunk000R, block453RightR]
  have hyc : y ∈ Icc (block453RightChunk000L : ℝ) (block453RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block453_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block453_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block453LeftL : ℝ) (block453LeftR : ℝ) →
    y ≠ 0 → y ≠ (block453S1 : ℝ) → y ≠ (block453S2 : ℝ) →
    y ≠ (block453S3 : ℝ) → y ≠ (block453S4 : ℝ) → 0 < block453V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block453RightL : ℝ) (block453RightR : ℝ) →
    y ≠ 0 → y ≠ (block453S1 : ℝ) → y ≠ (block453S2 : ℝ) →
    y ≠ (block453S3 : ℝ) → y ≠ (block453S4 : ℝ) → 0 < block453V y)

theorem block453_reallog_certificate_proof :
    block453_reallog_certificate := by
  exact ⟨block453_left_V_pos, block453_right_V_pos⟩

end Block453
end M1817475
end Erdos1038Lean
