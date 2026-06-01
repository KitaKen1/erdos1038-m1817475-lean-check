import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block506

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block506

open Set

def block506W1 : Rat := ((2231064644632919 : Rat) / 5000000000000000)
def block506W2 : Rat := (0 : Rat)
def block506W3 : Rat := ((1068479714760179 : Rat) / 2500000000000000)
def block506W4 : Rat := ((2419475423069219 : Rat) / 200000000000000000)
def block506S1 : Rat := ((18174751 : Rat) / 10000000)
def block506S2 : Rat := ((511587 : Rat) / 200000)
def block506S3 : Rat := ((130241709017857143011 : Rat) / 50000000000000000000)
def block506S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block506V (y : ℝ) : ℝ :=
  ratPotential block506W1 block506W2 block506W3 block506W4 block506S1 block506S2 block506S3 block506S4 y

def block506LeftParamsCertificate : Bool :=
  allBoxesSameParams block506LeftBoxes block506W1 block506W2 block506W3 block506W4 block506S1 block506S2 block506S3 block506S4

theorem block506LeftParamsCertificate_eq_true :
    block506LeftParamsCertificate = true := by
  native_decide

theorem block506_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block506LeftL : ℝ) (block506LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block506S1 : ℝ))
    (hy2ne : y ≠ (block506S2 : ℝ))
    (hy3ne : y ≠ (block506S3 : ℝ))
    (hy4ne : y ≠ (block506S4 : ℝ)) :
    0 < block506V y := by
  have hcert := block506LeftCertificate_eq_true
  unfold block506LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block506LeftBoxes) (lo := block506LeftL) (hi := block506LeftR)
    (w1 := block506W1) (w2 := block506W2) (w3 := block506W3) (w4 := block506W4)
    (s1 := block506S1) (s2 := block506S2) (s3 := block506S3) (s4 := block506S4)
    hboxes hcover block506LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block506RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block506RightChunk000 block506W1 block506W2 block506W3 block506W4 block506S1 block506S2 block506S3 block506S4

theorem block506RightChunk000ParamsCertificate_eq_true :
    block506RightChunk000ParamsCertificate = true := by
  native_decide

theorem block506_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block506RightChunk000L : ℝ) (block506RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block506S1 : ℝ))
    (hy2ne : y ≠ (block506S2 : ℝ))
    (hy3ne : y ≠ (block506S3 : ℝ))
    (hy4ne : y ≠ (block506S4 : ℝ)) :
    0 < block506V y := by
  have hcert := block506RightChunk000Certificate_eq_true
  unfold block506RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block506RightChunk000) (lo := block506RightChunk000L) (hi := block506RightChunk000R)
    (w1 := block506W1) (w2 := block506W2) (w3 := block506W3) (w4 := block506W4)
    (s1 := block506S1) (s2 := block506S2) (s3 := block506S3) (s4 := block506S4)
    hboxes hcover block506RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block506_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block506RightL : ℝ) (block506RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block506S1 : ℝ))
    (hy2ne : y ≠ (block506S2 : ℝ))
    (hy3ne : y ≠ (block506S3 : ℝ))
    (hy4ne : y ≠ (block506S4 : ℝ)) :
    0 < block506V y := by
  have hL : (block506RightChunk000L : ℝ) = (block506RightL : ℝ) := by
    norm_num [block506RightChunk000L, block506RightL]
  have hR : (block506RightChunk000R : ℝ) = (block506RightR : ℝ) := by
    norm_num [block506RightChunk000R, block506RightR]
  have hyc : y ∈ Icc (block506RightChunk000L : ℝ) (block506RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block506_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block506_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block506LeftL : ℝ) (block506LeftR : ℝ) →
    y ≠ 0 → y ≠ (block506S1 : ℝ) → y ≠ (block506S2 : ℝ) →
    y ≠ (block506S3 : ℝ) → y ≠ (block506S4 : ℝ) → 0 < block506V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block506RightL : ℝ) (block506RightR : ℝ) →
    y ≠ 0 → y ≠ (block506S1 : ℝ) → y ≠ (block506S2 : ℝ) →
    y ≠ (block506S3 : ℝ) → y ≠ (block506S4 : ℝ) → 0 < block506V y)

theorem block506_reallog_certificate_proof :
    block506_reallog_certificate := by
  exact ⟨block506_left_V_pos, block506_right_V_pos⟩

end Block506
end M1817475
end Erdos1038Lean
