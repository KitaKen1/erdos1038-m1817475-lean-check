import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block443

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block443

open Set

def block443W1 : Rat := ((193021397130143 : Rat) / 312500000000000)
def block443W2 : Rat := (0 : Rat)
def block443W3 : Rat := ((3238421893302369 : Rat) / 10000000000000000)
def block443W4 : Rat := ((3595068108996559 : Rat) / 50000000000000000)
def block443S1 : Rat := ((18174751 : Rat) / 10000000)
def block443S2 : Rat := ((511587 : Rat) / 200000)
def block443S3 : Rat := ((131473302767857142957 : Rat) / 50000000000000000000)
def block443S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block443V (y : ℝ) : ℝ :=
  ratPotential block443W1 block443W2 block443W3 block443W4 block443S1 block443S2 block443S3 block443S4 y

def block443LeftParamsCertificate : Bool :=
  allBoxesSameParams block443LeftBoxes block443W1 block443W2 block443W3 block443W4 block443S1 block443S2 block443S3 block443S4

theorem block443LeftParamsCertificate_eq_true :
    block443LeftParamsCertificate = true := by
  native_decide

theorem block443_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block443LeftL : ℝ) (block443LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block443S1 : ℝ))
    (hy2ne : y ≠ (block443S2 : ℝ))
    (hy3ne : y ≠ (block443S3 : ℝ))
    (hy4ne : y ≠ (block443S4 : ℝ)) :
    0 < block443V y := by
  have hcert := block443LeftCertificate_eq_true
  unfold block443LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block443LeftBoxes) (lo := block443LeftL) (hi := block443LeftR)
    (w1 := block443W1) (w2 := block443W2) (w3 := block443W3) (w4 := block443W4)
    (s1 := block443S1) (s2 := block443S2) (s3 := block443S3) (s4 := block443S4)
    hboxes hcover block443LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block443RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block443RightChunk000 block443W1 block443W2 block443W3 block443W4 block443S1 block443S2 block443S3 block443S4

theorem block443RightChunk000ParamsCertificate_eq_true :
    block443RightChunk000ParamsCertificate = true := by
  native_decide

theorem block443_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block443RightChunk000L : ℝ) (block443RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block443S1 : ℝ))
    (hy2ne : y ≠ (block443S2 : ℝ))
    (hy3ne : y ≠ (block443S3 : ℝ))
    (hy4ne : y ≠ (block443S4 : ℝ)) :
    0 < block443V y := by
  have hcert := block443RightChunk000Certificate_eq_true
  unfold block443RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block443RightChunk000) (lo := block443RightChunk000L) (hi := block443RightChunk000R)
    (w1 := block443W1) (w2 := block443W2) (w3 := block443W3) (w4 := block443W4)
    (s1 := block443S1) (s2 := block443S2) (s3 := block443S3) (s4 := block443S4)
    hboxes hcover block443RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block443_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block443RightL : ℝ) (block443RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block443S1 : ℝ))
    (hy2ne : y ≠ (block443S2 : ℝ))
    (hy3ne : y ≠ (block443S3 : ℝ))
    (hy4ne : y ≠ (block443S4 : ℝ)) :
    0 < block443V y := by
  have hL : (block443RightChunk000L : ℝ) = (block443RightL : ℝ) := by
    norm_num [block443RightChunk000L, block443RightL]
  have hR : (block443RightChunk000R : ℝ) = (block443RightR : ℝ) := by
    norm_num [block443RightChunk000R, block443RightR]
  have hyc : y ∈ Icc (block443RightChunk000L : ℝ) (block443RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block443_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block443_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block443LeftL : ℝ) (block443LeftR : ℝ) →
    y ≠ 0 → y ≠ (block443S1 : ℝ) → y ≠ (block443S2 : ℝ) →
    y ≠ (block443S3 : ℝ) → y ≠ (block443S4 : ℝ) → 0 < block443V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block443RightL : ℝ) (block443RightR : ℝ) →
    y ≠ 0 → y ≠ (block443S1 : ℝ) → y ≠ (block443S2 : ℝ) →
    y ≠ (block443S3 : ℝ) → y ≠ (block443S4 : ℝ) → 0 < block443V y)

theorem block443_reallog_certificate_proof :
    block443_reallog_certificate := by
  exact ⟨block443_left_V_pos, block443_right_V_pos⟩

end Block443
end M1817475
end Erdos1038Lean
