import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block273

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block273

open Set

def block273W1 : Rat := ((514429471796169 : Rat) / 500000000000000)
def block273W2 : Rat := ((7586040460190767 : Rat) / 250000000000000000)
def block273W3 : Rat := ((2910534163404731 : Rat) / 10000000000000000)
def block273W4 : Rat := (0 : Rat)
def block273S1 : Rat := ((18174751 : Rat) / 10000000)
def block273S2 : Rat := ((511587 : Rat) / 200000)
def block273S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block273S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block273V (y : ℝ) : ℝ :=
  ratPotential block273W1 block273W2 block273W3 block273W4 block273S1 block273S2 block273S3 block273S4 y

def block273LeftParamsCertificate : Bool :=
  allBoxesSameParams block273LeftBoxes block273W1 block273W2 block273W3 block273W4 block273S1 block273S2 block273S3 block273S4

theorem block273LeftParamsCertificate_eq_true :
    block273LeftParamsCertificate = true := by
  native_decide

theorem block273_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block273LeftL : ℝ) (block273LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block273S1 : ℝ))
    (hy2ne : y ≠ (block273S2 : ℝ))
    (hy3ne : y ≠ (block273S3 : ℝ))
    (hy4ne : y ≠ (block273S4 : ℝ)) :
    0 < block273V y := by
  have hcert := block273LeftCertificate_eq_true
  unfold block273LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block273LeftBoxes) (lo := block273LeftL) (hi := block273LeftR)
    (w1 := block273W1) (w2 := block273W2) (w3 := block273W3) (w4 := block273W4)
    (s1 := block273S1) (s2 := block273S2) (s3 := block273S3) (s4 := block273S4)
    hboxes hcover block273LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block273RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block273RightChunk000 block273W1 block273W2 block273W3 block273W4 block273S1 block273S2 block273S3 block273S4

theorem block273RightChunk000ParamsCertificate_eq_true :
    block273RightChunk000ParamsCertificate = true := by
  native_decide

theorem block273_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block273RightChunk000L : ℝ) (block273RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block273S1 : ℝ))
    (hy2ne : y ≠ (block273S2 : ℝ))
    (hy3ne : y ≠ (block273S3 : ℝ))
    (hy4ne : y ≠ (block273S4 : ℝ)) :
    0 < block273V y := by
  have hcert := block273RightChunk000Certificate_eq_true
  unfold block273RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block273RightChunk000) (lo := block273RightChunk000L) (hi := block273RightChunk000R)
    (w1 := block273W1) (w2 := block273W2) (w3 := block273W3) (w4 := block273W4)
    (s1 := block273S1) (s2 := block273S2) (s3 := block273S3) (s4 := block273S4)
    hboxes hcover block273RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block273_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block273RightL : ℝ) (block273RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block273S1 : ℝ))
    (hy2ne : y ≠ (block273S2 : ℝ))
    (hy3ne : y ≠ (block273S3 : ℝ))
    (hy4ne : y ≠ (block273S4 : ℝ)) :
    0 < block273V y := by
  have hL : (block273RightChunk000L : ℝ) = (block273RightL : ℝ) := by
    norm_num [block273RightChunk000L, block273RightL]
  have hR : (block273RightChunk000R : ℝ) = (block273RightR : ℝ) := by
    norm_num [block273RightChunk000R, block273RightR]
  have hyc : y ∈ Icc (block273RightChunk000L : ℝ) (block273RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block273_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block273_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block273LeftL : ℝ) (block273LeftR : ℝ) →
    y ≠ 0 → y ≠ (block273S1 : ℝ) → y ≠ (block273S2 : ℝ) →
    y ≠ (block273S3 : ℝ) → y ≠ (block273S4 : ℝ) → 0 < block273V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block273RightL : ℝ) (block273RightR : ℝ) →
    y ≠ 0 → y ≠ (block273S1 : ℝ) → y ≠ (block273S2 : ℝ) →
    y ≠ (block273S3 : ℝ) → y ≠ (block273S4 : ℝ) → 0 < block273V y)

theorem block273_reallog_certificate_proof :
    block273_reallog_certificate := by
  exact ⟨block273_left_V_pos, block273_right_V_pos⟩

end Block273
end M1817475
end Erdos1038Lean
