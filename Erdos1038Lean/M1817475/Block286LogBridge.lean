import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block286

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block286

open Set

def block286W1 : Rat := ((10284494188386173 : Rat) / 10000000000000000)
def block286W2 : Rat := ((7196619832282479 : Rat) / 200000000000000000)
def block286W3 : Rat := ((2824037972166861 : Rat) / 10000000000000000)
def block286W4 : Rat := (0 : Rat)
def block286S1 : Rat := ((18174751 : Rat) / 10000000)
def block286S2 : Rat := ((511587 : Rat) / 200000)
def block286S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block286S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block286V (y : ℝ) : ℝ :=
  ratPotential block286W1 block286W2 block286W3 block286W4 block286S1 block286S2 block286S3 block286S4 y

def block286LeftParamsCertificate : Bool :=
  allBoxesSameParams block286LeftBoxes block286W1 block286W2 block286W3 block286W4 block286S1 block286S2 block286S3 block286S4

theorem block286LeftParamsCertificate_eq_true :
    block286LeftParamsCertificate = true := by
  native_decide

theorem block286_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block286LeftL : ℝ) (block286LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block286S1 : ℝ))
    (hy2ne : y ≠ (block286S2 : ℝ))
    (hy3ne : y ≠ (block286S3 : ℝ))
    (hy4ne : y ≠ (block286S4 : ℝ)) :
    0 < block286V y := by
  have hcert := block286LeftCertificate_eq_true
  unfold block286LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block286LeftBoxes) (lo := block286LeftL) (hi := block286LeftR)
    (w1 := block286W1) (w2 := block286W2) (w3 := block286W3) (w4 := block286W4)
    (s1 := block286S1) (s2 := block286S2) (s3 := block286S3) (s4 := block286S4)
    hboxes hcover block286LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block286RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block286RightChunk000 block286W1 block286W2 block286W3 block286W4 block286S1 block286S2 block286S3 block286S4

theorem block286RightChunk000ParamsCertificate_eq_true :
    block286RightChunk000ParamsCertificate = true := by
  native_decide

theorem block286_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block286RightChunk000L : ℝ) (block286RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block286S1 : ℝ))
    (hy2ne : y ≠ (block286S2 : ℝ))
    (hy3ne : y ≠ (block286S3 : ℝ))
    (hy4ne : y ≠ (block286S4 : ℝ)) :
    0 < block286V y := by
  have hcert := block286RightChunk000Certificate_eq_true
  unfold block286RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block286RightChunk000) (lo := block286RightChunk000L) (hi := block286RightChunk000R)
    (w1 := block286W1) (w2 := block286W2) (w3 := block286W3) (w4 := block286W4)
    (s1 := block286S1) (s2 := block286S2) (s3 := block286S3) (s4 := block286S4)
    hboxes hcover block286RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block286_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block286RightL : ℝ) (block286RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block286S1 : ℝ))
    (hy2ne : y ≠ (block286S2 : ℝ))
    (hy3ne : y ≠ (block286S3 : ℝ))
    (hy4ne : y ≠ (block286S4 : ℝ)) :
    0 < block286V y := by
  have hL : (block286RightChunk000L : ℝ) = (block286RightL : ℝ) := by
    norm_num [block286RightChunk000L, block286RightL]
  have hR : (block286RightChunk000R : ℝ) = (block286RightR : ℝ) := by
    norm_num [block286RightChunk000R, block286RightR]
  have hyc : y ∈ Icc (block286RightChunk000L : ℝ) (block286RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block286_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block286_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block286LeftL : ℝ) (block286LeftR : ℝ) →
    y ≠ 0 → y ≠ (block286S1 : ℝ) → y ≠ (block286S2 : ℝ) →
    y ≠ (block286S3 : ℝ) → y ≠ (block286S4 : ℝ) → 0 < block286V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block286RightL : ℝ) (block286RightR : ℝ) →
    y ≠ 0 → y ≠ (block286S1 : ℝ) → y ≠ (block286S2 : ℝ) →
    y ≠ (block286S3 : ℝ) → y ≠ (block286S4 : ℝ) → 0 < block286V y)

theorem block286_reallog_certificate_proof :
    block286_reallog_certificate := by
  exact ⟨block286_left_V_pos, block286_right_V_pos⟩

end Block286
end M1817475
end Erdos1038Lean
