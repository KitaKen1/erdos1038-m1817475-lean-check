import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block126

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block126

open Set

def block126W1 : Rat := ((12835280921937129 : Rat) / 5000000000000000)
def block126W2 : Rat := (0 : Rat)
def block126W3 : Rat := ((9937885040708253 : Rat) / 100000000000000000)
def block126W4 : Rat := ((715343210218669 : Rat) / 5000000000000000)
def block126S1 : Rat := ((18174751 : Rat) / 10000000)
def block126S2 : Rat := ((511587 : Rat) / 200000)
def block126S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block126S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block126V (y : ℝ) : ℝ :=
  ratPotential block126W1 block126W2 block126W3 block126W4 block126S1 block126S2 block126S3 block126S4 y

def block126LeftParamsCertificate : Bool :=
  allBoxesSameParams block126LeftBoxes block126W1 block126W2 block126W3 block126W4 block126S1 block126S2 block126S3 block126S4

theorem block126LeftParamsCertificate_eq_true :
    block126LeftParamsCertificate = true := by
  native_decide

theorem block126_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block126LeftL : ℝ) (block126LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block126S1 : ℝ))
    (hy2ne : y ≠ (block126S2 : ℝ))
    (hy3ne : y ≠ (block126S3 : ℝ))
    (hy4ne : y ≠ (block126S4 : ℝ)) :
    0 < block126V y := by
  have hcert := block126LeftCertificate_eq_true
  unfold block126LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block126LeftBoxes) (lo := block126LeftL) (hi := block126LeftR)
    (w1 := block126W1) (w2 := block126W2) (w3 := block126W3) (w4 := block126W4)
    (s1 := block126S1) (s2 := block126S2) (s3 := block126S3) (s4 := block126S4)
    hboxes hcover block126LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block126RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block126RightChunk000 block126W1 block126W2 block126W3 block126W4 block126S1 block126S2 block126S3 block126S4

theorem block126RightChunk000ParamsCertificate_eq_true :
    block126RightChunk000ParamsCertificate = true := by
  native_decide

theorem block126_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block126RightChunk000L : ℝ) (block126RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block126S1 : ℝ))
    (hy2ne : y ≠ (block126S2 : ℝ))
    (hy3ne : y ≠ (block126S3 : ℝ))
    (hy4ne : y ≠ (block126S4 : ℝ)) :
    0 < block126V y := by
  have hcert := block126RightChunk000Certificate_eq_true
  unfold block126RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block126RightChunk000) (lo := block126RightChunk000L) (hi := block126RightChunk000R)
    (w1 := block126W1) (w2 := block126W2) (w3 := block126W3) (w4 := block126W4)
    (s1 := block126S1) (s2 := block126S2) (s3 := block126S3) (s4 := block126S4)
    hboxes hcover block126RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block126_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block126RightL : ℝ) (block126RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block126S1 : ℝ))
    (hy2ne : y ≠ (block126S2 : ℝ))
    (hy3ne : y ≠ (block126S3 : ℝ))
    (hy4ne : y ≠ (block126S4 : ℝ)) :
    0 < block126V y := by
  have hL : (block126RightChunk000L : ℝ) = (block126RightL : ℝ) := by
    norm_num [block126RightChunk000L, block126RightL]
  have hR : (block126RightChunk000R : ℝ) = (block126RightR : ℝ) := by
    norm_num [block126RightChunk000R, block126RightR]
  have hyc : y ∈ Icc (block126RightChunk000L : ℝ) (block126RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block126_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block126_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block126LeftL : ℝ) (block126LeftR : ℝ) →
    y ≠ 0 → y ≠ (block126S1 : ℝ) → y ≠ (block126S2 : ℝ) →
    y ≠ (block126S3 : ℝ) → y ≠ (block126S4 : ℝ) → 0 < block126V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block126RightL : ℝ) (block126RightR : ℝ) →
    y ≠ 0 → y ≠ (block126S1 : ℝ) → y ≠ (block126S2 : ℝ) →
    y ≠ (block126S3 : ℝ) → y ≠ (block126S4 : ℝ) → 0 < block126V y)

theorem block126_reallog_certificate_proof :
    block126_reallog_certificate := by
  exact ⟨block126_left_V_pos, block126_right_V_pos⟩

end Block126
end M1817475
end Erdos1038Lean
