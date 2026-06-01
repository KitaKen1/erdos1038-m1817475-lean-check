import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block526

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block526

open Set

def block526W1 : Rat := ((4119876498725451 : Rat) / 10000000000000000)
def block526W2 : Rat := (0 : Rat)
def block526W3 : Rat := ((4506761289354519 : Rat) / 10000000000000000)
def block526W4 : Rat := (0 : Rat)
def block526S1 : Rat := ((18174751 : Rat) / 10000000)
def block526S2 : Rat := ((511587 : Rat) / 200000)
def block526S3 : Rat := ((129850726875000000171 : Rat) / 50000000000000000000)
def block526S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block526V (y : ℝ) : ℝ :=
  ratPotential block526W1 block526W2 block526W3 block526W4 block526S1 block526S2 block526S3 block526S4 y

def block526LeftParamsCertificate : Bool :=
  allBoxesSameParams block526LeftBoxes block526W1 block526W2 block526W3 block526W4 block526S1 block526S2 block526S3 block526S4

theorem block526LeftParamsCertificate_eq_true :
    block526LeftParamsCertificate = true := by
  native_decide

theorem block526_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block526LeftL : ℝ) (block526LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block526S1 : ℝ))
    (hy2ne : y ≠ (block526S2 : ℝ))
    (hy3ne : y ≠ (block526S3 : ℝ))
    (hy4ne : y ≠ (block526S4 : ℝ)) :
    0 < block526V y := by
  have hcert := block526LeftCertificate_eq_true
  unfold block526LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block526LeftBoxes) (lo := block526LeftL) (hi := block526LeftR)
    (w1 := block526W1) (w2 := block526W2) (w3 := block526W3) (w4 := block526W4)
    (s1 := block526S1) (s2 := block526S2) (s3 := block526S3) (s4 := block526S4)
    hboxes hcover block526LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block526RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block526RightChunk000 block526W1 block526W2 block526W3 block526W4 block526S1 block526S2 block526S3 block526S4

theorem block526RightChunk000ParamsCertificate_eq_true :
    block526RightChunk000ParamsCertificate = true := by
  native_decide

theorem block526_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block526RightChunk000L : ℝ) (block526RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block526S1 : ℝ))
    (hy2ne : y ≠ (block526S2 : ℝ))
    (hy3ne : y ≠ (block526S3 : ℝ))
    (hy4ne : y ≠ (block526S4 : ℝ)) :
    0 < block526V y := by
  have hcert := block526RightChunk000Certificate_eq_true
  unfold block526RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block526RightChunk000) (lo := block526RightChunk000L) (hi := block526RightChunk000R)
    (w1 := block526W1) (w2 := block526W2) (w3 := block526W3) (w4 := block526W4)
    (s1 := block526S1) (s2 := block526S2) (s3 := block526S3) (s4 := block526S4)
    hboxes hcover block526RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block526_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block526RightL : ℝ) (block526RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block526S1 : ℝ))
    (hy2ne : y ≠ (block526S2 : ℝ))
    (hy3ne : y ≠ (block526S3 : ℝ))
    (hy4ne : y ≠ (block526S4 : ℝ)) :
    0 < block526V y := by
  have hL : (block526RightChunk000L : ℝ) = (block526RightL : ℝ) := by
    norm_num [block526RightChunk000L, block526RightL]
  have hR : (block526RightChunk000R : ℝ) = (block526RightR : ℝ) := by
    norm_num [block526RightChunk000R, block526RightR]
  have hyc : y ∈ Icc (block526RightChunk000L : ℝ) (block526RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block526_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block526_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block526LeftL : ℝ) (block526LeftR : ℝ) →
    y ≠ 0 → y ≠ (block526S1 : ℝ) → y ≠ (block526S2 : ℝ) →
    y ≠ (block526S3 : ℝ) → y ≠ (block526S4 : ℝ) → 0 < block526V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block526RightL : ℝ) (block526RightR : ℝ) →
    y ≠ 0 → y ≠ (block526S1 : ℝ) → y ≠ (block526S2 : ℝ) →
    y ≠ (block526S3 : ℝ) → y ≠ (block526S4 : ℝ) → 0 < block526V y)

theorem block526_reallog_certificate_proof :
    block526_reallog_certificate := by
  exact ⟨block526_left_V_pos, block526_right_V_pos⟩

end Block526
end M1817475
end Erdos1038Lean
