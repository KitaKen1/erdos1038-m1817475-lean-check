import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block421

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block421

open Set

def block421W1 : Rat := ((1709280858511049 : Rat) / 2500000000000000)
def block421W2 : Rat := (0 : Rat)
def block421W3 : Rat := ((297827575885721 : Rat) / 1000000000000000)
def block421W4 : Rat := ((4224741710678209 : Rat) / 50000000000000000)
def block421S1 : Rat := ((18174751 : Rat) / 10000000)
def block421S2 : Rat := ((511587 : Rat) / 200000)
def block421S3 : Rat := ((131903383125000000081 : Rat) / 50000000000000000000)
def block421S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block421V (y : ℝ) : ℝ :=
  ratPotential block421W1 block421W2 block421W3 block421W4 block421S1 block421S2 block421S3 block421S4 y

def block421LeftParamsCertificate : Bool :=
  allBoxesSameParams block421LeftBoxes block421W1 block421W2 block421W3 block421W4 block421S1 block421S2 block421S3 block421S4

theorem block421LeftParamsCertificate_eq_true :
    block421LeftParamsCertificate = true := by
  native_decide

theorem block421_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block421LeftL : ℝ) (block421LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block421S1 : ℝ))
    (hy2ne : y ≠ (block421S2 : ℝ))
    (hy3ne : y ≠ (block421S3 : ℝ))
    (hy4ne : y ≠ (block421S4 : ℝ)) :
    0 < block421V y := by
  have hcert := block421LeftCertificate_eq_true
  unfold block421LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block421LeftBoxes) (lo := block421LeftL) (hi := block421LeftR)
    (w1 := block421W1) (w2 := block421W2) (w3 := block421W3) (w4 := block421W4)
    (s1 := block421S1) (s2 := block421S2) (s3 := block421S3) (s4 := block421S4)
    hboxes hcover block421LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block421RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block421RightChunk000 block421W1 block421W2 block421W3 block421W4 block421S1 block421S2 block421S3 block421S4

theorem block421RightChunk000ParamsCertificate_eq_true :
    block421RightChunk000ParamsCertificate = true := by
  native_decide

theorem block421_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block421RightChunk000L : ℝ) (block421RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block421S1 : ℝ))
    (hy2ne : y ≠ (block421S2 : ℝ))
    (hy3ne : y ≠ (block421S3 : ℝ))
    (hy4ne : y ≠ (block421S4 : ℝ)) :
    0 < block421V y := by
  have hcert := block421RightChunk000Certificate_eq_true
  unfold block421RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block421RightChunk000) (lo := block421RightChunk000L) (hi := block421RightChunk000R)
    (w1 := block421W1) (w2 := block421W2) (w3 := block421W3) (w4 := block421W4)
    (s1 := block421S1) (s2 := block421S2) (s3 := block421S3) (s4 := block421S4)
    hboxes hcover block421RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block421_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block421RightL : ℝ) (block421RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block421S1 : ℝ))
    (hy2ne : y ≠ (block421S2 : ℝ))
    (hy3ne : y ≠ (block421S3 : ℝ))
    (hy4ne : y ≠ (block421S4 : ℝ)) :
    0 < block421V y := by
  have hL : (block421RightChunk000L : ℝ) = (block421RightL : ℝ) := by
    norm_num [block421RightChunk000L, block421RightL]
  have hR : (block421RightChunk000R : ℝ) = (block421RightR : ℝ) := by
    norm_num [block421RightChunk000R, block421RightR]
  have hyc : y ∈ Icc (block421RightChunk000L : ℝ) (block421RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block421_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block421_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block421LeftL : ℝ) (block421LeftR : ℝ) →
    y ≠ 0 → y ≠ (block421S1 : ℝ) → y ≠ (block421S2 : ℝ) →
    y ≠ (block421S3 : ℝ) → y ≠ (block421S4 : ℝ) → 0 < block421V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block421RightL : ℝ) (block421RightR : ℝ) →
    y ≠ 0 → y ≠ (block421S1 : ℝ) → y ≠ (block421S2 : ℝ) →
    y ≠ (block421S3 : ℝ) → y ≠ (block421S4 : ℝ) → 0 < block421V y)

theorem block421_reallog_certificate_proof :
    block421_reallog_certificate := by
  exact ⟨block421_left_V_pos, block421_right_V_pos⟩

end Block421
end M1817475
end Erdos1038Lean
