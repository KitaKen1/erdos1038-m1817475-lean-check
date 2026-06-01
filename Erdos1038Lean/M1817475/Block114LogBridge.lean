import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block114

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block114

open Set

def block114W1 : Rat := ((12267883931392767 : Rat) / 5000000000000000)
def block114W2 : Rat := (0 : Rat)
def block114W3 : Rat := ((7514703947671 : Rat) / 100000000000000)
def block114W4 : Rat := ((8638305315609121 : Rat) / 50000000000000000)
def block114S1 : Rat := ((18174751 : Rat) / 10000000)
def block114S2 : Rat := ((511587 : Rat) / 200000)
def block114S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block114S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block114V (y : ℝ) : ℝ :=
  ratPotential block114W1 block114W2 block114W3 block114W4 block114S1 block114S2 block114S3 block114S4 y

def block114LeftParamsCertificate : Bool :=
  allBoxesSameParams block114LeftBoxes block114W1 block114W2 block114W3 block114W4 block114S1 block114S2 block114S3 block114S4

theorem block114LeftParamsCertificate_eq_true :
    block114LeftParamsCertificate = true := by
  native_decide

theorem block114_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block114LeftL : ℝ) (block114LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block114S1 : ℝ))
    (hy2ne : y ≠ (block114S2 : ℝ))
    (hy3ne : y ≠ (block114S3 : ℝ))
    (hy4ne : y ≠ (block114S4 : ℝ)) :
    0 < block114V y := by
  have hcert := block114LeftCertificate_eq_true
  unfold block114LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block114LeftBoxes) (lo := block114LeftL) (hi := block114LeftR)
    (w1 := block114W1) (w2 := block114W2) (w3 := block114W3) (w4 := block114W4)
    (s1 := block114S1) (s2 := block114S2) (s3 := block114S3) (s4 := block114S4)
    hboxes hcover block114LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block114RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block114RightChunk000 block114W1 block114W2 block114W3 block114W4 block114S1 block114S2 block114S3 block114S4

theorem block114RightChunk000ParamsCertificate_eq_true :
    block114RightChunk000ParamsCertificate = true := by
  native_decide

theorem block114_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block114RightChunk000L : ℝ) (block114RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block114S1 : ℝ))
    (hy2ne : y ≠ (block114S2 : ℝ))
    (hy3ne : y ≠ (block114S3 : ℝ))
    (hy4ne : y ≠ (block114S4 : ℝ)) :
    0 < block114V y := by
  have hcert := block114RightChunk000Certificate_eq_true
  unfold block114RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block114RightChunk000) (lo := block114RightChunk000L) (hi := block114RightChunk000R)
    (w1 := block114W1) (w2 := block114W2) (w3 := block114W3) (w4 := block114W4)
    (s1 := block114S1) (s2 := block114S2) (s3 := block114S3) (s4 := block114S4)
    hboxes hcover block114RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block114_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block114RightL : ℝ) (block114RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block114S1 : ℝ))
    (hy2ne : y ≠ (block114S2 : ℝ))
    (hy3ne : y ≠ (block114S3 : ℝ))
    (hy4ne : y ≠ (block114S4 : ℝ)) :
    0 < block114V y := by
  have hL : (block114RightChunk000L : ℝ) = (block114RightL : ℝ) := by
    norm_num [block114RightChunk000L, block114RightL]
  have hR : (block114RightChunk000R : ℝ) = (block114RightR : ℝ) := by
    norm_num [block114RightChunk000R, block114RightR]
  have hyc : y ∈ Icc (block114RightChunk000L : ℝ) (block114RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block114_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block114_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block114LeftL : ℝ) (block114LeftR : ℝ) →
    y ≠ 0 → y ≠ (block114S1 : ℝ) → y ≠ (block114S2 : ℝ) →
    y ≠ (block114S3 : ℝ) → y ≠ (block114S4 : ℝ) → 0 < block114V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block114RightL : ℝ) (block114RightR : ℝ) →
    y ≠ 0 → y ≠ (block114S1 : ℝ) → y ≠ (block114S2 : ℝ) →
    y ≠ (block114S3 : ℝ) → y ≠ (block114S4 : ℝ) → 0 < block114V y)

theorem block114_reallog_certificate_proof :
    block114_reallog_certificate := by
  exact ⟨block114_left_V_pos, block114_right_V_pos⟩

end Block114
end M1817475
end Erdos1038Lean
