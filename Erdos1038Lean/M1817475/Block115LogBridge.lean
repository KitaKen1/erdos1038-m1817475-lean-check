import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block115

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block115

open Set

def block115W1 : Rat := ((2432442790679131 : Rat) / 1000000000000000)
def block115W2 : Rat := (0 : Rat)
def block115W3 : Rat := ((3893788440275933 : Rat) / 50000000000000000)
def block115W4 : Rat := ((3409059371509559 : Rat) / 20000000000000000)
def block115S1 : Rat := ((18174751 : Rat) / 10000000)
def block115S2 : Rat := ((511587 : Rat) / 200000)
def block115S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block115S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block115V (y : ℝ) : ℝ :=
  ratPotential block115W1 block115W2 block115W3 block115W4 block115S1 block115S2 block115S3 block115S4 y

def block115LeftParamsCertificate : Bool :=
  allBoxesSameParams block115LeftBoxes block115W1 block115W2 block115W3 block115W4 block115S1 block115S2 block115S3 block115S4

theorem block115LeftParamsCertificate_eq_true :
    block115LeftParamsCertificate = true := by
  native_decide

theorem block115_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block115LeftL : ℝ) (block115LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block115S1 : ℝ))
    (hy2ne : y ≠ (block115S2 : ℝ))
    (hy3ne : y ≠ (block115S3 : ℝ))
    (hy4ne : y ≠ (block115S4 : ℝ)) :
    0 < block115V y := by
  have hcert := block115LeftCertificate_eq_true
  unfold block115LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block115LeftBoxes) (lo := block115LeftL) (hi := block115LeftR)
    (w1 := block115W1) (w2 := block115W2) (w3 := block115W3) (w4 := block115W4)
    (s1 := block115S1) (s2 := block115S2) (s3 := block115S3) (s4 := block115S4)
    hboxes hcover block115LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block115RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block115RightChunk000 block115W1 block115W2 block115W3 block115W4 block115S1 block115S2 block115S3 block115S4

theorem block115RightChunk000ParamsCertificate_eq_true :
    block115RightChunk000ParamsCertificate = true := by
  native_decide

theorem block115_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block115RightChunk000L : ℝ) (block115RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block115S1 : ℝ))
    (hy2ne : y ≠ (block115S2 : ℝ))
    (hy3ne : y ≠ (block115S3 : ℝ))
    (hy4ne : y ≠ (block115S4 : ℝ)) :
    0 < block115V y := by
  have hcert := block115RightChunk000Certificate_eq_true
  unfold block115RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block115RightChunk000) (lo := block115RightChunk000L) (hi := block115RightChunk000R)
    (w1 := block115W1) (w2 := block115W2) (w3 := block115W3) (w4 := block115W4)
    (s1 := block115S1) (s2 := block115S2) (s3 := block115S3) (s4 := block115S4)
    hboxes hcover block115RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block115_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block115RightL : ℝ) (block115RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block115S1 : ℝ))
    (hy2ne : y ≠ (block115S2 : ℝ))
    (hy3ne : y ≠ (block115S3 : ℝ))
    (hy4ne : y ≠ (block115S4 : ℝ)) :
    0 < block115V y := by
  have hL : (block115RightChunk000L : ℝ) = (block115RightL : ℝ) := by
    norm_num [block115RightChunk000L, block115RightL]
  have hR : (block115RightChunk000R : ℝ) = (block115RightR : ℝ) := by
    norm_num [block115RightChunk000R, block115RightR]
  have hyc : y ∈ Icc (block115RightChunk000L : ℝ) (block115RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block115_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block115_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block115LeftL : ℝ) (block115LeftR : ℝ) →
    y ≠ 0 → y ≠ (block115S1 : ℝ) → y ≠ (block115S2 : ℝ) →
    y ≠ (block115S3 : ℝ) → y ≠ (block115S4 : ℝ) → 0 < block115V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block115RightL : ℝ) (block115RightR : ℝ) →
    y ≠ 0 → y ≠ (block115S1 : ℝ) → y ≠ (block115S2 : ℝ) →
    y ≠ (block115S3 : ℝ) → y ≠ (block115S4 : ℝ) → 0 < block115V y)

theorem block115_reallog_certificate_proof :
    block115_reallog_certificate := by
  exact ⟨block115_left_V_pos, block115_right_V_pos⟩

end Block115
end M1817475
end Erdos1038Lean
