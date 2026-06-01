import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block132

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block132

open Set

def block132W1 : Rat := ((1272281909326527 : Rat) / 500000000000000)
def block132W2 : Rat := (0 : Rat)
def block132W3 : Rat := ((2726116396725839 : Rat) / 25000000000000000)
def block132W4 : Rat := ((13208350673116437 : Rat) / 100000000000000000)
def block132S1 : Rat := ((18174751 : Rat) / 10000000)
def block132S2 : Rat := ((511587 : Rat) / 200000)
def block132S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block132S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block132V (y : ℝ) : ℝ :=
  ratPotential block132W1 block132W2 block132W3 block132W4 block132S1 block132S2 block132S3 block132S4 y

def block132LeftParamsCertificate : Bool :=
  allBoxesSameParams block132LeftBoxes block132W1 block132W2 block132W3 block132W4 block132S1 block132S2 block132S3 block132S4

theorem block132LeftParamsCertificate_eq_true :
    block132LeftParamsCertificate = true := by
  native_decide

theorem block132_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block132LeftL : ℝ) (block132LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block132S1 : ℝ))
    (hy2ne : y ≠ (block132S2 : ℝ))
    (hy3ne : y ≠ (block132S3 : ℝ))
    (hy4ne : y ≠ (block132S4 : ℝ)) :
    0 < block132V y := by
  have hcert := block132LeftCertificate_eq_true
  unfold block132LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block132LeftBoxes) (lo := block132LeftL) (hi := block132LeftR)
    (w1 := block132W1) (w2 := block132W2) (w3 := block132W3) (w4 := block132W4)
    (s1 := block132S1) (s2 := block132S2) (s3 := block132S3) (s4 := block132S4)
    hboxes hcover block132LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block132RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block132RightChunk000 block132W1 block132W2 block132W3 block132W4 block132S1 block132S2 block132S3 block132S4

theorem block132RightChunk000ParamsCertificate_eq_true :
    block132RightChunk000ParamsCertificate = true := by
  native_decide

theorem block132_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block132RightChunk000L : ℝ) (block132RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block132S1 : ℝ))
    (hy2ne : y ≠ (block132S2 : ℝ))
    (hy3ne : y ≠ (block132S3 : ℝ))
    (hy4ne : y ≠ (block132S4 : ℝ)) :
    0 < block132V y := by
  have hcert := block132RightChunk000Certificate_eq_true
  unfold block132RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block132RightChunk000) (lo := block132RightChunk000L) (hi := block132RightChunk000R)
    (w1 := block132W1) (w2 := block132W2) (w3 := block132W3) (w4 := block132W4)
    (s1 := block132S1) (s2 := block132S2) (s3 := block132S3) (s4 := block132S4)
    hboxes hcover block132RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block132_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block132RightL : ℝ) (block132RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block132S1 : ℝ))
    (hy2ne : y ≠ (block132S2 : ℝ))
    (hy3ne : y ≠ (block132S3 : ℝ))
    (hy4ne : y ≠ (block132S4 : ℝ)) :
    0 < block132V y := by
  have hL : (block132RightChunk000L : ℝ) = (block132RightL : ℝ) := by
    norm_num [block132RightChunk000L, block132RightL]
  have hR : (block132RightChunk000R : ℝ) = (block132RightR : ℝ) := by
    norm_num [block132RightChunk000R, block132RightR]
  have hyc : y ∈ Icc (block132RightChunk000L : ℝ) (block132RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block132_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block132_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block132LeftL : ℝ) (block132LeftR : ℝ) →
    y ≠ 0 → y ≠ (block132S1 : ℝ) → y ≠ (block132S2 : ℝ) →
    y ≠ (block132S3 : ℝ) → y ≠ (block132S4 : ℝ) → 0 < block132V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block132RightL : ℝ) (block132RightR : ℝ) →
    y ≠ 0 → y ≠ (block132S1 : ℝ) → y ≠ (block132S2 : ℝ) →
    y ≠ (block132S3 : ℝ) → y ≠ (block132S4 : ℝ) → 0 < block132V y)

theorem block132_reallog_certificate_proof :
    block132_reallog_certificate := by
  exact ⟨block132_left_V_pos, block132_right_V_pos⟩

end Block132
end M1817475
end Erdos1038Lean
