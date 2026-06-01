import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block499

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block499

open Set

def block499W1 : Rat := ((2320703006777913 : Rat) / 5000000000000000)
def block499W2 : Rat := (0 : Rat)
def block499W3 : Rat := ((10331495622833961 : Rat) / 25000000000000000)
def block499W4 : Rat := ((5222605769112253 : Rat) / 250000000000000000)
def block499S1 : Rat := ((18174751 : Rat) / 10000000)
def block499S2 : Rat := ((511587 : Rat) / 200000)
def block499S3 : Rat := ((26075710553571428601 : Rat) / 10000000000000000000)
def block499S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block499V (y : ℝ) : ℝ :=
  ratPotential block499W1 block499W2 block499W3 block499W4 block499S1 block499S2 block499S3 block499S4 y

def block499LeftParamsCertificate : Bool :=
  allBoxesSameParams block499LeftBoxes block499W1 block499W2 block499W3 block499W4 block499S1 block499S2 block499S3 block499S4

theorem block499LeftParamsCertificate_eq_true :
    block499LeftParamsCertificate = true := by
  native_decide

theorem block499_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block499LeftL : ℝ) (block499LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block499S1 : ℝ))
    (hy2ne : y ≠ (block499S2 : ℝ))
    (hy3ne : y ≠ (block499S3 : ℝ))
    (hy4ne : y ≠ (block499S4 : ℝ)) :
    0 < block499V y := by
  have hcert := block499LeftCertificate_eq_true
  unfold block499LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block499LeftBoxes) (lo := block499LeftL) (hi := block499LeftR)
    (w1 := block499W1) (w2 := block499W2) (w3 := block499W3) (w4 := block499W4)
    (s1 := block499S1) (s2 := block499S2) (s3 := block499S3) (s4 := block499S4)
    hboxes hcover block499LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block499RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block499RightChunk000 block499W1 block499W2 block499W3 block499W4 block499S1 block499S2 block499S3 block499S4

theorem block499RightChunk000ParamsCertificate_eq_true :
    block499RightChunk000ParamsCertificate = true := by
  native_decide

theorem block499_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block499RightChunk000L : ℝ) (block499RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block499S1 : ℝ))
    (hy2ne : y ≠ (block499S2 : ℝ))
    (hy3ne : y ≠ (block499S3 : ℝ))
    (hy4ne : y ≠ (block499S4 : ℝ)) :
    0 < block499V y := by
  have hcert := block499RightChunk000Certificate_eq_true
  unfold block499RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block499RightChunk000) (lo := block499RightChunk000L) (hi := block499RightChunk000R)
    (w1 := block499W1) (w2 := block499W2) (w3 := block499W3) (w4 := block499W4)
    (s1 := block499S1) (s2 := block499S2) (s3 := block499S3) (s4 := block499S4)
    hboxes hcover block499RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block499_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block499RightL : ℝ) (block499RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block499S1 : ℝ))
    (hy2ne : y ≠ (block499S2 : ℝ))
    (hy3ne : y ≠ (block499S3 : ℝ))
    (hy4ne : y ≠ (block499S4 : ℝ)) :
    0 < block499V y := by
  have hL : (block499RightChunk000L : ℝ) = (block499RightL : ℝ) := by
    norm_num [block499RightChunk000L, block499RightL]
  have hR : (block499RightChunk000R : ℝ) = (block499RightR : ℝ) := by
    norm_num [block499RightChunk000R, block499RightR]
  have hyc : y ∈ Icc (block499RightChunk000L : ℝ) (block499RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block499_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block499_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block499LeftL : ℝ) (block499LeftR : ℝ) →
    y ≠ 0 → y ≠ (block499S1 : ℝ) → y ≠ (block499S2 : ℝ) →
    y ≠ (block499S3 : ℝ) → y ≠ (block499S4 : ℝ) → 0 < block499V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block499RightL : ℝ) (block499RightR : ℝ) →
    y ≠ 0 → y ≠ (block499S1 : ℝ) → y ≠ (block499S2 : ℝ) →
    y ≠ (block499S3 : ℝ) → y ≠ (block499S4 : ℝ) → 0 < block499V y)

theorem block499_reallog_certificate_proof :
    block499_reallog_certificate := by
  exact ⟨block499_left_V_pos, block499_right_V_pos⟩

end Block499
end M1817475
end Erdos1038Lean
