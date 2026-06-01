import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block293

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block293

open Set

def block293W1 : Rat := ((10186720630879913 : Rat) / 10000000000000000)
def block293W2 : Rat := ((1018191810341533 : Rat) / 25000000000000000)
def block293W3 : Rat := ((6926427743006451 : Rat) / 25000000000000000)
def block293W4 : Rat := (0 : Rat)
def block293S1 : Rat := ((18174751 : Rat) / 10000000)
def block293S2 : Rat := ((511587 : Rat) / 200000)
def block293S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block293S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block293V (y : ℝ) : ℝ :=
  ratPotential block293W1 block293W2 block293W3 block293W4 block293S1 block293S2 block293S3 block293S4 y

def block293LeftParamsCertificate : Bool :=
  allBoxesSameParams block293LeftBoxes block293W1 block293W2 block293W3 block293W4 block293S1 block293S2 block293S3 block293S4

theorem block293LeftParamsCertificate_eq_true :
    block293LeftParamsCertificate = true := by
  native_decide

theorem block293_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block293LeftL : ℝ) (block293LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block293S1 : ℝ))
    (hy2ne : y ≠ (block293S2 : ℝ))
    (hy3ne : y ≠ (block293S3 : ℝ))
    (hy4ne : y ≠ (block293S4 : ℝ)) :
    0 < block293V y := by
  have hcert := block293LeftCertificate_eq_true
  unfold block293LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block293LeftBoxes) (lo := block293LeftL) (hi := block293LeftR)
    (w1 := block293W1) (w2 := block293W2) (w3 := block293W3) (w4 := block293W4)
    (s1 := block293S1) (s2 := block293S2) (s3 := block293S3) (s4 := block293S4)
    hboxes hcover block293LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block293RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block293RightChunk000 block293W1 block293W2 block293W3 block293W4 block293S1 block293S2 block293S3 block293S4

theorem block293RightChunk000ParamsCertificate_eq_true :
    block293RightChunk000ParamsCertificate = true := by
  native_decide

theorem block293_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block293RightChunk000L : ℝ) (block293RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block293S1 : ℝ))
    (hy2ne : y ≠ (block293S2 : ℝ))
    (hy3ne : y ≠ (block293S3 : ℝ))
    (hy4ne : y ≠ (block293S4 : ℝ)) :
    0 < block293V y := by
  have hcert := block293RightChunk000Certificate_eq_true
  unfold block293RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block293RightChunk000) (lo := block293RightChunk000L) (hi := block293RightChunk000R)
    (w1 := block293W1) (w2 := block293W2) (w3 := block293W3) (w4 := block293W4)
    (s1 := block293S1) (s2 := block293S2) (s3 := block293S3) (s4 := block293S4)
    hboxes hcover block293RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block293_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block293RightL : ℝ) (block293RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block293S1 : ℝ))
    (hy2ne : y ≠ (block293S2 : ℝ))
    (hy3ne : y ≠ (block293S3 : ℝ))
    (hy4ne : y ≠ (block293S4 : ℝ)) :
    0 < block293V y := by
  have hL : (block293RightChunk000L : ℝ) = (block293RightL : ℝ) := by
    norm_num [block293RightChunk000L, block293RightL]
  have hR : (block293RightChunk000R : ℝ) = (block293RightR : ℝ) := by
    norm_num [block293RightChunk000R, block293RightR]
  have hyc : y ∈ Icc (block293RightChunk000L : ℝ) (block293RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block293_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block293_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block293LeftL : ℝ) (block293LeftR : ℝ) →
    y ≠ 0 → y ≠ (block293S1 : ℝ) → y ≠ (block293S2 : ℝ) →
    y ≠ (block293S3 : ℝ) → y ≠ (block293S4 : ℝ) → 0 < block293V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block293RightL : ℝ) (block293RightR : ℝ) →
    y ≠ 0 → y ≠ (block293S1 : ℝ) → y ≠ (block293S2 : ℝ) →
    y ≠ (block293S3 : ℝ) → y ≠ (block293S4 : ℝ) → 0 < block293V y)

theorem block293_reallog_certificate_proof :
    block293_reallog_certificate := by
  exact ⟨block293_left_V_pos, block293_right_V_pos⟩

end Block293
end M1817475
end Erdos1038Lean
