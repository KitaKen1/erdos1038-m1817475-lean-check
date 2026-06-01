import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block145

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block145

open Set

def block145W1 : Rat := ((295544046086577 : Rat) / 125000000000000)
def block145W2 : Rat := (0 : Rat)
def block145W3 : Rat := ((14248045382498387 : Rat) / 100000000000000000)
def block145W4 : Rat := ((10187380828521611 : Rat) / 100000000000000000)
def block145S1 : Rat := ((18174751 : Rat) / 10000000)
def block145S2 : Rat := ((511587 : Rat) / 200000)
def block145S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block145S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block145V (y : ℝ) : ℝ :=
  ratPotential block145W1 block145W2 block145W3 block145W4 block145S1 block145S2 block145S3 block145S4 y

def block145LeftParamsCertificate : Bool :=
  allBoxesSameParams block145LeftBoxes block145W1 block145W2 block145W3 block145W4 block145S1 block145S2 block145S3 block145S4

theorem block145LeftParamsCertificate_eq_true :
    block145LeftParamsCertificate = true := by
  native_decide

theorem block145_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block145LeftL : ℝ) (block145LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block145S1 : ℝ))
    (hy2ne : y ≠ (block145S2 : ℝ))
    (hy3ne : y ≠ (block145S3 : ℝ))
    (hy4ne : y ≠ (block145S4 : ℝ)) :
    0 < block145V y := by
  have hcert := block145LeftCertificate_eq_true
  unfold block145LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block145LeftBoxes) (lo := block145LeftL) (hi := block145LeftR)
    (w1 := block145W1) (w2 := block145W2) (w3 := block145W3) (w4 := block145W4)
    (s1 := block145S1) (s2 := block145S2) (s3 := block145S3) (s4 := block145S4)
    hboxes hcover block145LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block145RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block145RightChunk000 block145W1 block145W2 block145W3 block145W4 block145S1 block145S2 block145S3 block145S4

theorem block145RightChunk000ParamsCertificate_eq_true :
    block145RightChunk000ParamsCertificate = true := by
  native_decide

theorem block145_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block145RightChunk000L : ℝ) (block145RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block145S1 : ℝ))
    (hy2ne : y ≠ (block145S2 : ℝ))
    (hy3ne : y ≠ (block145S3 : ℝ))
    (hy4ne : y ≠ (block145S4 : ℝ)) :
    0 < block145V y := by
  have hcert := block145RightChunk000Certificate_eq_true
  unfold block145RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block145RightChunk000) (lo := block145RightChunk000L) (hi := block145RightChunk000R)
    (w1 := block145W1) (w2 := block145W2) (w3 := block145W3) (w4 := block145W4)
    (s1 := block145S1) (s2 := block145S2) (s3 := block145S3) (s4 := block145S4)
    hboxes hcover block145RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block145_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block145RightL : ℝ) (block145RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block145S1 : ℝ))
    (hy2ne : y ≠ (block145S2 : ℝ))
    (hy3ne : y ≠ (block145S3 : ℝ))
    (hy4ne : y ≠ (block145S4 : ℝ)) :
    0 < block145V y := by
  have hL : (block145RightChunk000L : ℝ) = (block145RightL : ℝ) := by
    norm_num [block145RightChunk000L, block145RightL]
  have hR : (block145RightChunk000R : ℝ) = (block145RightR : ℝ) := by
    norm_num [block145RightChunk000R, block145RightR]
  have hyc : y ∈ Icc (block145RightChunk000L : ℝ) (block145RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block145_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block145_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block145LeftL : ℝ) (block145LeftR : ℝ) →
    y ≠ 0 → y ≠ (block145S1 : ℝ) → y ≠ (block145S2 : ℝ) →
    y ≠ (block145S3 : ℝ) → y ≠ (block145S4 : ℝ) → 0 < block145V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block145RightL : ℝ) (block145RightR : ℝ) →
    y ≠ 0 → y ≠ (block145S1 : ℝ) → y ≠ (block145S2 : ℝ) →
    y ≠ (block145S3 : ℝ) → y ≠ (block145S4 : ℝ) → 0 < block145V y)

theorem block145_reallog_certificate_proof :
    block145_reallog_certificate := by
  exact ⟨block145_left_V_pos, block145_right_V_pos⟩

end Block145
end M1817475
end Erdos1038Lean
