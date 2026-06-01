import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block142

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block142

open Set

def block142W1 : Rat := ((24751160135098567 : Rat) / 10000000000000000)
def block142W2 : Rat := (0 : Rat)
def block142W3 : Rat := ((401307041781181 : Rat) / 3125000000000000)
def block142W4 : Rat := ((5598612039011487 : Rat) / 50000000000000000)
def block142S1 : Rat := ((18174751 : Rat) / 10000000)
def block142S2 : Rat := ((511587 : Rat) / 200000)
def block142S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block142S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block142V (y : ℝ) : ℝ :=
  ratPotential block142W1 block142W2 block142W3 block142W4 block142S1 block142S2 block142S3 block142S4 y

def block142LeftParamsCertificate : Bool :=
  allBoxesSameParams block142LeftBoxes block142W1 block142W2 block142W3 block142W4 block142S1 block142S2 block142S3 block142S4

theorem block142LeftParamsCertificate_eq_true :
    block142LeftParamsCertificate = true := by
  native_decide

theorem block142_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block142LeftL : ℝ) (block142LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block142S1 : ℝ))
    (hy2ne : y ≠ (block142S2 : ℝ))
    (hy3ne : y ≠ (block142S3 : ℝ))
    (hy4ne : y ≠ (block142S4 : ℝ)) :
    0 < block142V y := by
  have hcert := block142LeftCertificate_eq_true
  unfold block142LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block142LeftBoxes) (lo := block142LeftL) (hi := block142LeftR)
    (w1 := block142W1) (w2 := block142W2) (w3 := block142W3) (w4 := block142W4)
    (s1 := block142S1) (s2 := block142S2) (s3 := block142S3) (s4 := block142S4)
    hboxes hcover block142LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block142RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block142RightChunk000 block142W1 block142W2 block142W3 block142W4 block142S1 block142S2 block142S3 block142S4

theorem block142RightChunk000ParamsCertificate_eq_true :
    block142RightChunk000ParamsCertificate = true := by
  native_decide

theorem block142_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block142RightChunk000L : ℝ) (block142RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block142S1 : ℝ))
    (hy2ne : y ≠ (block142S2 : ℝ))
    (hy3ne : y ≠ (block142S3 : ℝ))
    (hy4ne : y ≠ (block142S4 : ℝ)) :
    0 < block142V y := by
  have hcert := block142RightChunk000Certificate_eq_true
  unfold block142RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block142RightChunk000) (lo := block142RightChunk000L) (hi := block142RightChunk000R)
    (w1 := block142W1) (w2 := block142W2) (w3 := block142W3) (w4 := block142W4)
    (s1 := block142S1) (s2 := block142S2) (s3 := block142S3) (s4 := block142S4)
    hboxes hcover block142RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block142_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block142RightL : ℝ) (block142RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block142S1 : ℝ))
    (hy2ne : y ≠ (block142S2 : ℝ))
    (hy3ne : y ≠ (block142S3 : ℝ))
    (hy4ne : y ≠ (block142S4 : ℝ)) :
    0 < block142V y := by
  have hL : (block142RightChunk000L : ℝ) = (block142RightL : ℝ) := by
    norm_num [block142RightChunk000L, block142RightL]
  have hR : (block142RightChunk000R : ℝ) = (block142RightR : ℝ) := by
    norm_num [block142RightChunk000R, block142RightR]
  have hyc : y ∈ Icc (block142RightChunk000L : ℝ) (block142RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block142_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block142_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block142LeftL : ℝ) (block142LeftR : ℝ) →
    y ≠ 0 → y ≠ (block142S1 : ℝ) → y ≠ (block142S2 : ℝ) →
    y ≠ (block142S3 : ℝ) → y ≠ (block142S4 : ℝ) → 0 < block142V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block142RightL : ℝ) (block142RightR : ℝ) →
    y ≠ 0 → y ≠ (block142S1 : ℝ) → y ≠ (block142S2 : ℝ) →
    y ≠ (block142S3 : ℝ) → y ≠ (block142S4 : ℝ) → 0 < block142V y)

theorem block142_reallog_certificate_proof :
    block142_reallog_certificate := by
  exact ⟨block142_left_V_pos, block142_right_V_pos⟩

end Block142
end M1817475
end Erdos1038Lean
