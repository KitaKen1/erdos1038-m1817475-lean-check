import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block288

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block288

open Set

def block288W1 : Rat := ((2571733236303051 : Rat) / 2500000000000000)
def block288W2 : Rat := ((3681077862335379 : Rat) / 100000000000000000)
def block288W3 : Rat := ((281083352301233 : Rat) / 1000000000000000)
def block288W4 : Rat := (0 : Rat)
def block288S1 : Rat := ((18174751 : Rat) / 10000000)
def block288S2 : Rat := ((511587 : Rat) / 200000)
def block288S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block288S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block288V (y : ℝ) : ℝ :=
  ratPotential block288W1 block288W2 block288W3 block288W4 block288S1 block288S2 block288S3 block288S4 y

def block288LeftParamsCertificate : Bool :=
  allBoxesSameParams block288LeftBoxes block288W1 block288W2 block288W3 block288W4 block288S1 block288S2 block288S3 block288S4

theorem block288LeftParamsCertificate_eq_true :
    block288LeftParamsCertificate = true := by
  native_decide

theorem block288_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block288LeftL : ℝ) (block288LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block288S1 : ℝ))
    (hy2ne : y ≠ (block288S2 : ℝ))
    (hy3ne : y ≠ (block288S3 : ℝ))
    (hy4ne : y ≠ (block288S4 : ℝ)) :
    0 < block288V y := by
  have hcert := block288LeftCertificate_eq_true
  unfold block288LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block288LeftBoxes) (lo := block288LeftL) (hi := block288LeftR)
    (w1 := block288W1) (w2 := block288W2) (w3 := block288W3) (w4 := block288W4)
    (s1 := block288S1) (s2 := block288S2) (s3 := block288S3) (s4 := block288S4)
    hboxes hcover block288LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block288RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block288RightChunk000 block288W1 block288W2 block288W3 block288W4 block288S1 block288S2 block288S3 block288S4

theorem block288RightChunk000ParamsCertificate_eq_true :
    block288RightChunk000ParamsCertificate = true := by
  native_decide

theorem block288_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block288RightChunk000L : ℝ) (block288RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block288S1 : ℝ))
    (hy2ne : y ≠ (block288S2 : ℝ))
    (hy3ne : y ≠ (block288S3 : ℝ))
    (hy4ne : y ≠ (block288S4 : ℝ)) :
    0 < block288V y := by
  have hcert := block288RightChunk000Certificate_eq_true
  unfold block288RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block288RightChunk000) (lo := block288RightChunk000L) (hi := block288RightChunk000R)
    (w1 := block288W1) (w2 := block288W2) (w3 := block288W3) (w4 := block288W4)
    (s1 := block288S1) (s2 := block288S2) (s3 := block288S3) (s4 := block288S4)
    hboxes hcover block288RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block288_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block288RightL : ℝ) (block288RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block288S1 : ℝ))
    (hy2ne : y ≠ (block288S2 : ℝ))
    (hy3ne : y ≠ (block288S3 : ℝ))
    (hy4ne : y ≠ (block288S4 : ℝ)) :
    0 < block288V y := by
  have hL : (block288RightChunk000L : ℝ) = (block288RightL : ℝ) := by
    norm_num [block288RightChunk000L, block288RightL]
  have hR : (block288RightChunk000R : ℝ) = (block288RightR : ℝ) := by
    norm_num [block288RightChunk000R, block288RightR]
  have hyc : y ∈ Icc (block288RightChunk000L : ℝ) (block288RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block288_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block288_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block288LeftL : ℝ) (block288LeftR : ℝ) →
    y ≠ 0 → y ≠ (block288S1 : ℝ) → y ≠ (block288S2 : ℝ) →
    y ≠ (block288S3 : ℝ) → y ≠ (block288S4 : ℝ) → 0 < block288V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block288RightL : ℝ) (block288RightR : ℝ) →
    y ≠ 0 → y ≠ (block288S1 : ℝ) → y ≠ (block288S2 : ℝ) →
    y ≠ (block288S3 : ℝ) → y ≠ (block288S4 : ℝ) → 0 < block288V y)

theorem block288_reallog_certificate_proof :
    block288_reallog_certificate := by
  exact ⟨block288_left_V_pos, block288_right_V_pos⟩

end Block288
end M1817475
end Erdos1038Lean
