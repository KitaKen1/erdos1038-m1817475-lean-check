import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block304

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block304

open Set

def block304W1 : Rat := ((987632613031961 : Rat) / 1000000000000000)
def block304W2 : Rat := ((2568856547877627 : Rat) / 50000000000000000)
def block304W3 : Rat := ((6684264386132109 : Rat) / 25000000000000000)
def block304W4 : Rat := (0 : Rat)
def block304S1 : Rat := ((18174751 : Rat) / 10000000)
def block304S2 : Rat := ((511587 : Rat) / 200000)
def block304S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block304S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block304V (y : ℝ) : ℝ :=
  ratPotential block304W1 block304W2 block304W3 block304W4 block304S1 block304S2 block304S3 block304S4 y

def block304LeftParamsCertificate : Bool :=
  allBoxesSameParams block304LeftBoxes block304W1 block304W2 block304W3 block304W4 block304S1 block304S2 block304S3 block304S4

theorem block304LeftParamsCertificate_eq_true :
    block304LeftParamsCertificate = true := by
  native_decide

theorem block304_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block304LeftL : ℝ) (block304LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block304S1 : ℝ))
    (hy2ne : y ≠ (block304S2 : ℝ))
    (hy3ne : y ≠ (block304S3 : ℝ))
    (hy4ne : y ≠ (block304S4 : ℝ)) :
    0 < block304V y := by
  have hcert := block304LeftCertificate_eq_true
  unfold block304LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block304LeftBoxes) (lo := block304LeftL) (hi := block304LeftR)
    (w1 := block304W1) (w2 := block304W2) (w3 := block304W3) (w4 := block304W4)
    (s1 := block304S1) (s2 := block304S2) (s3 := block304S3) (s4 := block304S4)
    hboxes hcover block304LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block304RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block304RightChunk000 block304W1 block304W2 block304W3 block304W4 block304S1 block304S2 block304S3 block304S4

theorem block304RightChunk000ParamsCertificate_eq_true :
    block304RightChunk000ParamsCertificate = true := by
  native_decide

theorem block304_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block304RightChunk000L : ℝ) (block304RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block304S1 : ℝ))
    (hy2ne : y ≠ (block304S2 : ℝ))
    (hy3ne : y ≠ (block304S3 : ℝ))
    (hy4ne : y ≠ (block304S4 : ℝ)) :
    0 < block304V y := by
  have hcert := block304RightChunk000Certificate_eq_true
  unfold block304RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block304RightChunk000) (lo := block304RightChunk000L) (hi := block304RightChunk000R)
    (w1 := block304W1) (w2 := block304W2) (w3 := block304W3) (w4 := block304W4)
    (s1 := block304S1) (s2 := block304S2) (s3 := block304S3) (s4 := block304S4)
    hboxes hcover block304RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block304_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block304RightL : ℝ) (block304RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block304S1 : ℝ))
    (hy2ne : y ≠ (block304S2 : ℝ))
    (hy3ne : y ≠ (block304S3 : ℝ))
    (hy4ne : y ≠ (block304S4 : ℝ)) :
    0 < block304V y := by
  have hL : (block304RightChunk000L : ℝ) = (block304RightL : ℝ) := by
    norm_num [block304RightChunk000L, block304RightL]
  have hR : (block304RightChunk000R : ℝ) = (block304RightR : ℝ) := by
    norm_num [block304RightChunk000R, block304RightR]
  have hyc : y ∈ Icc (block304RightChunk000L : ℝ) (block304RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block304_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block304_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block304LeftL : ℝ) (block304LeftR : ℝ) →
    y ≠ 0 → y ≠ (block304S1 : ℝ) → y ≠ (block304S2 : ℝ) →
    y ≠ (block304S3 : ℝ) → y ≠ (block304S4 : ℝ) → 0 < block304V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block304RightL : ℝ) (block304RightR : ℝ) →
    y ≠ 0 → y ≠ (block304S1 : ℝ) → y ≠ (block304S2 : ℝ) →
    y ≠ (block304S3 : ℝ) → y ≠ (block304S4 : ℝ) → 0 < block304V y)

theorem block304_reallog_certificate_proof :
    block304_reallog_certificate := by
  exact ⟨block304_left_V_pos, block304_right_V_pos⟩

end Block304
end M1817475
end Erdos1038Lean
