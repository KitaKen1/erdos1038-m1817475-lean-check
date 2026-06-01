import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block322

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block322

open Set

def block322W1 : Rat := ((2338217357674797 : Rat) / 2500000000000000)
def block322W2 : Rat := ((7065654993332379 : Rat) / 100000000000000000)
def block322W3 : Rat := ((12534770265854983 : Rat) / 50000000000000000)
def block322W4 : Rat := (0 : Rat)
def block322S1 : Rat := ((18174751 : Rat) / 10000000)
def block322S2 : Rat := ((511587 : Rat) / 200000)
def block322S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block322S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block322V (y : ℝ) : ℝ :=
  ratPotential block322W1 block322W2 block322W3 block322W4 block322S1 block322S2 block322S3 block322S4 y

def block322LeftParamsCertificate : Bool :=
  allBoxesSameParams block322LeftBoxes block322W1 block322W2 block322W3 block322W4 block322S1 block322S2 block322S3 block322S4

theorem block322LeftParamsCertificate_eq_true :
    block322LeftParamsCertificate = true := by
  native_decide

theorem block322_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block322LeftL : ℝ) (block322LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block322S1 : ℝ))
    (hy2ne : y ≠ (block322S2 : ℝ))
    (hy3ne : y ≠ (block322S3 : ℝ))
    (hy4ne : y ≠ (block322S4 : ℝ)) :
    0 < block322V y := by
  have hcert := block322LeftCertificate_eq_true
  unfold block322LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block322LeftBoxes) (lo := block322LeftL) (hi := block322LeftR)
    (w1 := block322W1) (w2 := block322W2) (w3 := block322W3) (w4 := block322W4)
    (s1 := block322S1) (s2 := block322S2) (s3 := block322S3) (s4 := block322S4)
    hboxes hcover block322LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block322RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block322RightChunk000 block322W1 block322W2 block322W3 block322W4 block322S1 block322S2 block322S3 block322S4

theorem block322RightChunk000ParamsCertificate_eq_true :
    block322RightChunk000ParamsCertificate = true := by
  native_decide

theorem block322_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block322RightChunk000L : ℝ) (block322RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block322S1 : ℝ))
    (hy2ne : y ≠ (block322S2 : ℝ))
    (hy3ne : y ≠ (block322S3 : ℝ))
    (hy4ne : y ≠ (block322S4 : ℝ)) :
    0 < block322V y := by
  have hcert := block322RightChunk000Certificate_eq_true
  unfold block322RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block322RightChunk000) (lo := block322RightChunk000L) (hi := block322RightChunk000R)
    (w1 := block322W1) (w2 := block322W2) (w3 := block322W3) (w4 := block322W4)
    (s1 := block322S1) (s2 := block322S2) (s3 := block322S3) (s4 := block322S4)
    hboxes hcover block322RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block322_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block322RightL : ℝ) (block322RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block322S1 : ℝ))
    (hy2ne : y ≠ (block322S2 : ℝ))
    (hy3ne : y ≠ (block322S3 : ℝ))
    (hy4ne : y ≠ (block322S4 : ℝ)) :
    0 < block322V y := by
  have hL : (block322RightChunk000L : ℝ) = (block322RightL : ℝ) := by
    norm_num [block322RightChunk000L, block322RightL]
  have hR : (block322RightChunk000R : ℝ) = (block322RightR : ℝ) := by
    norm_num [block322RightChunk000R, block322RightR]
  have hyc : y ∈ Icc (block322RightChunk000L : ℝ) (block322RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block322_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block322_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block322LeftL : ℝ) (block322LeftR : ℝ) →
    y ≠ 0 → y ≠ (block322S1 : ℝ) → y ≠ (block322S2 : ℝ) →
    y ≠ (block322S3 : ℝ) → y ≠ (block322S4 : ℝ) → 0 < block322V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block322RightL : ℝ) (block322RightR : ℝ) →
    y ≠ 0 → y ≠ (block322S1 : ℝ) → y ≠ (block322S2 : ℝ) →
    y ≠ (block322S3 : ℝ) → y ≠ (block322S4 : ℝ) → 0 < block322V y)

theorem block322_reallog_certificate_proof :
    block322_reallog_certificate := by
  exact ⟨block322_left_V_pos, block322_right_V_pos⟩

end Block322
end M1817475
end Erdos1038Lean
