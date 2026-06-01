import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block103

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block103

open Set

def block103W1 : Rat := ((1301006206102837 : Rat) / 500000000000000)
def block103W2 : Rat := (0 : Rat)
def block103W3 : Rat := ((5288998559095253 : Rat) / 100000000000000000)
def block103W4 : Rat := ((1942852696150447 : Rat) / 10000000000000000)
def block103S1 : Rat := ((18174751 : Rat) / 10000000)
def block103S2 : Rat := ((511587 : Rat) / 200000)
def block103S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block103S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block103V (y : ℝ) : ℝ :=
  ratPotential block103W1 block103W2 block103W3 block103W4 block103S1 block103S2 block103S3 block103S4 y

def block103LeftParamsCertificate : Bool :=
  allBoxesSameParams block103LeftBoxes block103W1 block103W2 block103W3 block103W4 block103S1 block103S2 block103S3 block103S4

theorem block103LeftParamsCertificate_eq_true :
    block103LeftParamsCertificate = true := by
  native_decide

theorem block103_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block103LeftL : ℝ) (block103LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block103S1 : ℝ))
    (hy2ne : y ≠ (block103S2 : ℝ))
    (hy3ne : y ≠ (block103S3 : ℝ))
    (hy4ne : y ≠ (block103S4 : ℝ)) :
    0 < block103V y := by
  have hcert := block103LeftCertificate_eq_true
  unfold block103LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block103LeftBoxes) (lo := block103LeftL) (hi := block103LeftR)
    (w1 := block103W1) (w2 := block103W2) (w3 := block103W3) (w4 := block103W4)
    (s1 := block103S1) (s2 := block103S2) (s3 := block103S3) (s4 := block103S4)
    hboxes hcover block103LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block103RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block103RightChunk000 block103W1 block103W2 block103W3 block103W4 block103S1 block103S2 block103S3 block103S4

theorem block103RightChunk000ParamsCertificate_eq_true :
    block103RightChunk000ParamsCertificate = true := by
  native_decide

theorem block103_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block103RightChunk000L : ℝ) (block103RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block103S1 : ℝ))
    (hy2ne : y ≠ (block103S2 : ℝ))
    (hy3ne : y ≠ (block103S3 : ℝ))
    (hy4ne : y ≠ (block103S4 : ℝ)) :
    0 < block103V y := by
  have hcert := block103RightChunk000Certificate_eq_true
  unfold block103RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block103RightChunk000) (lo := block103RightChunk000L) (hi := block103RightChunk000R)
    (w1 := block103W1) (w2 := block103W2) (w3 := block103W3) (w4 := block103W4)
    (s1 := block103S1) (s2 := block103S2) (s3 := block103S3) (s4 := block103S4)
    hboxes hcover block103RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block103_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block103RightL : ℝ) (block103RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block103S1 : ℝ))
    (hy2ne : y ≠ (block103S2 : ℝ))
    (hy3ne : y ≠ (block103S3 : ℝ))
    (hy4ne : y ≠ (block103S4 : ℝ)) :
    0 < block103V y := by
  have hL : (block103RightChunk000L : ℝ) = (block103RightL : ℝ) := by
    norm_num [block103RightChunk000L, block103RightL]
  have hR : (block103RightChunk000R : ℝ) = (block103RightR : ℝ) := by
    norm_num [block103RightChunk000R, block103RightR]
  have hyc : y ∈ Icc (block103RightChunk000L : ℝ) (block103RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block103_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block103_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block103LeftL : ℝ) (block103LeftR : ℝ) →
    y ≠ 0 → y ≠ (block103S1 : ℝ) → y ≠ (block103S2 : ℝ) →
    y ≠ (block103S3 : ℝ) → y ≠ (block103S4 : ℝ) → 0 < block103V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block103RightL : ℝ) (block103RightR : ℝ) →
    y ≠ 0 → y ≠ (block103S1 : ℝ) → y ≠ (block103S2 : ℝ) →
    y ≠ (block103S3 : ℝ) → y ≠ (block103S4 : ℝ) → 0 < block103V y)

theorem block103_reallog_certificate_proof :
    block103_reallog_certificate := by
  exact ⟨block103_left_V_pos, block103_right_V_pos⟩

end Block103
end M1817475
end Erdos1038Lean
