import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block164

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block164

open Set

def block164W1 : Rat := ((9231337195574053 : Rat) / 5000000000000000)
def block164W2 : Rat := (0 : Rat)
def block164W3 : Rat := ((8200037937388513 : Rat) / 50000000000000000)
def block164W4 : Rat := ((10386094401481963 : Rat) / 100000000000000000)
def block164S1 : Rat := ((18174751 : Rat) / 10000000)
def block164S2 : Rat := ((511587 : Rat) / 200000)
def block164S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block164S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block164V (y : ℝ) : ℝ :=
  ratPotential block164W1 block164W2 block164W3 block164W4 block164S1 block164S2 block164S3 block164S4 y

def block164LeftParamsCertificate : Bool :=
  allBoxesSameParams block164LeftBoxes block164W1 block164W2 block164W3 block164W4 block164S1 block164S2 block164S3 block164S4

theorem block164LeftParamsCertificate_eq_true :
    block164LeftParamsCertificate = true := by
  native_decide

theorem block164_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block164LeftL : ℝ) (block164LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block164S1 : ℝ))
    (hy2ne : y ≠ (block164S2 : ℝ))
    (hy3ne : y ≠ (block164S3 : ℝ))
    (hy4ne : y ≠ (block164S4 : ℝ)) :
    0 < block164V y := by
  have hcert := block164LeftCertificate_eq_true
  unfold block164LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block164LeftBoxes) (lo := block164LeftL) (hi := block164LeftR)
    (w1 := block164W1) (w2 := block164W2) (w3 := block164W3) (w4 := block164W4)
    (s1 := block164S1) (s2 := block164S2) (s3 := block164S3) (s4 := block164S4)
    hboxes hcover block164LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block164RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block164RightChunk000 block164W1 block164W2 block164W3 block164W4 block164S1 block164S2 block164S3 block164S4

theorem block164RightChunk000ParamsCertificate_eq_true :
    block164RightChunk000ParamsCertificate = true := by
  native_decide

theorem block164_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block164RightChunk000L : ℝ) (block164RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block164S1 : ℝ))
    (hy2ne : y ≠ (block164S2 : ℝ))
    (hy3ne : y ≠ (block164S3 : ℝ))
    (hy4ne : y ≠ (block164S4 : ℝ)) :
    0 < block164V y := by
  have hcert := block164RightChunk000Certificate_eq_true
  unfold block164RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block164RightChunk000) (lo := block164RightChunk000L) (hi := block164RightChunk000R)
    (w1 := block164W1) (w2 := block164W2) (w3 := block164W3) (w4 := block164W4)
    (s1 := block164S1) (s2 := block164S2) (s3 := block164S3) (s4 := block164S4)
    hboxes hcover block164RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block164_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block164RightL : ℝ) (block164RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block164S1 : ℝ))
    (hy2ne : y ≠ (block164S2 : ℝ))
    (hy3ne : y ≠ (block164S3 : ℝ))
    (hy4ne : y ≠ (block164S4 : ℝ)) :
    0 < block164V y := by
  have hL : (block164RightChunk000L : ℝ) = (block164RightL : ℝ) := by
    norm_num [block164RightChunk000L, block164RightL]
  have hR : (block164RightChunk000R : ℝ) = (block164RightR : ℝ) := by
    norm_num [block164RightChunk000R, block164RightR]
  have hyc : y ∈ Icc (block164RightChunk000L : ℝ) (block164RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block164_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block164_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block164LeftL : ℝ) (block164LeftR : ℝ) →
    y ≠ 0 → y ≠ (block164S1 : ℝ) → y ≠ (block164S2 : ℝ) →
    y ≠ (block164S3 : ℝ) → y ≠ (block164S4 : ℝ) → 0 < block164V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block164RightL : ℝ) (block164RightR : ℝ) →
    y ≠ 0 → y ≠ (block164S1 : ℝ) → y ≠ (block164S2 : ℝ) →
    y ≠ (block164S3 : ℝ) → y ≠ (block164S4 : ℝ) → 0 < block164V y)

theorem block164_reallog_certificate_proof :
    block164_reallog_certificate := by
  exact ⟨block164_left_V_pos, block164_right_V_pos⟩

end Block164
end M1817475
end Erdos1038Lean
