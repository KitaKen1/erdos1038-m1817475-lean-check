import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block108

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block108

open Set

def block108W1 : Rat := ((1288945804799577 : Rat) / 500000000000000)
def block108W2 : Rat := (0 : Rat)
def block108W3 : Rat := ((2982986860576437 : Rat) / 50000000000000000)
def block108W4 : Rat := ((744884796982209 : Rat) / 4000000000000000)
def block108S1 : Rat := ((18174751 : Rat) / 10000000)
def block108S2 : Rat := ((511587 : Rat) / 200000)
def block108S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block108S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block108V (y : ℝ) : ℝ :=
  ratPotential block108W1 block108W2 block108W3 block108W4 block108S1 block108S2 block108S3 block108S4 y

def block108LeftParamsCertificate : Bool :=
  allBoxesSameParams block108LeftBoxes block108W1 block108W2 block108W3 block108W4 block108S1 block108S2 block108S3 block108S4

theorem block108LeftParamsCertificate_eq_true :
    block108LeftParamsCertificate = true := by
  native_decide

theorem block108_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block108LeftL : ℝ) (block108LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block108S1 : ℝ))
    (hy2ne : y ≠ (block108S2 : ℝ))
    (hy3ne : y ≠ (block108S3 : ℝ))
    (hy4ne : y ≠ (block108S4 : ℝ)) :
    0 < block108V y := by
  have hcert := block108LeftCertificate_eq_true
  unfold block108LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block108LeftBoxes) (lo := block108LeftL) (hi := block108LeftR)
    (w1 := block108W1) (w2 := block108W2) (w3 := block108W3) (w4 := block108W4)
    (s1 := block108S1) (s2 := block108S2) (s3 := block108S3) (s4 := block108S4)
    hboxes hcover block108LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block108RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block108RightChunk000 block108W1 block108W2 block108W3 block108W4 block108S1 block108S2 block108S3 block108S4

theorem block108RightChunk000ParamsCertificate_eq_true :
    block108RightChunk000ParamsCertificate = true := by
  native_decide

theorem block108_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block108RightChunk000L : ℝ) (block108RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block108S1 : ℝ))
    (hy2ne : y ≠ (block108S2 : ℝ))
    (hy3ne : y ≠ (block108S3 : ℝ))
    (hy4ne : y ≠ (block108S4 : ℝ)) :
    0 < block108V y := by
  have hcert := block108RightChunk000Certificate_eq_true
  unfold block108RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block108RightChunk000) (lo := block108RightChunk000L) (hi := block108RightChunk000R)
    (w1 := block108W1) (w2 := block108W2) (w3 := block108W3) (w4 := block108W4)
    (s1 := block108S1) (s2 := block108S2) (s3 := block108S3) (s4 := block108S4)
    hboxes hcover block108RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block108_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block108RightL : ℝ) (block108RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block108S1 : ℝ))
    (hy2ne : y ≠ (block108S2 : ℝ))
    (hy3ne : y ≠ (block108S3 : ℝ))
    (hy4ne : y ≠ (block108S4 : ℝ)) :
    0 < block108V y := by
  have hL : (block108RightChunk000L : ℝ) = (block108RightL : ℝ) := by
    norm_num [block108RightChunk000L, block108RightL]
  have hR : (block108RightChunk000R : ℝ) = (block108RightR : ℝ) := by
    norm_num [block108RightChunk000R, block108RightR]
  have hyc : y ∈ Icc (block108RightChunk000L : ℝ) (block108RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block108_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block108_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block108LeftL : ℝ) (block108LeftR : ℝ) →
    y ≠ 0 → y ≠ (block108S1 : ℝ) → y ≠ (block108S2 : ℝ) →
    y ≠ (block108S3 : ℝ) → y ≠ (block108S4 : ℝ) → 0 < block108V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block108RightL : ℝ) (block108RightR : ℝ) →
    y ≠ 0 → y ≠ (block108S1 : ℝ) → y ≠ (block108S2 : ℝ) →
    y ≠ (block108S3 : ℝ) → y ≠ (block108S4 : ℝ) → 0 < block108V y)

theorem block108_reallog_certificate_proof :
    block108_reallog_certificate := by
  exact ⟨block108_left_V_pos, block108_right_V_pos⟩

end Block108
end M1817475
end Erdos1038Lean
