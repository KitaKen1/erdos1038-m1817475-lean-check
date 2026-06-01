import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block272

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block272

open Set

def block272W1 : Rat := ((1028799813652649 : Rat) / 1000000000000000)
def block272W2 : Rat := ((14965396420925113 : Rat) / 500000000000000000)
def block272W3 : Rat := ((1823177329733959 : Rat) / 6250000000000000)
def block272W4 : Rat := (0 : Rat)
def block272S1 : Rat := ((18174751 : Rat) / 10000000)
def block272S2 : Rat := ((511587 : Rat) / 200000)
def block272S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block272S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block272V (y : ℝ) : ℝ :=
  ratPotential block272W1 block272W2 block272W3 block272W4 block272S1 block272S2 block272S3 block272S4 y

def block272LeftParamsCertificate : Bool :=
  allBoxesSameParams block272LeftBoxes block272W1 block272W2 block272W3 block272W4 block272S1 block272S2 block272S3 block272S4

theorem block272LeftParamsCertificate_eq_true :
    block272LeftParamsCertificate = true := by
  native_decide

theorem block272_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block272LeftL : ℝ) (block272LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block272S1 : ℝ))
    (hy2ne : y ≠ (block272S2 : ℝ))
    (hy3ne : y ≠ (block272S3 : ℝ))
    (hy4ne : y ≠ (block272S4 : ℝ)) :
    0 < block272V y := by
  have hcert := block272LeftCertificate_eq_true
  unfold block272LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block272LeftBoxes) (lo := block272LeftL) (hi := block272LeftR)
    (w1 := block272W1) (w2 := block272W2) (w3 := block272W3) (w4 := block272W4)
    (s1 := block272S1) (s2 := block272S2) (s3 := block272S3) (s4 := block272S4)
    hboxes hcover block272LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block272RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block272RightChunk000 block272W1 block272W2 block272W3 block272W4 block272S1 block272S2 block272S3 block272S4

theorem block272RightChunk000ParamsCertificate_eq_true :
    block272RightChunk000ParamsCertificate = true := by
  native_decide

theorem block272_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block272RightChunk000L : ℝ) (block272RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block272S1 : ℝ))
    (hy2ne : y ≠ (block272S2 : ℝ))
    (hy3ne : y ≠ (block272S3 : ℝ))
    (hy4ne : y ≠ (block272S4 : ℝ)) :
    0 < block272V y := by
  have hcert := block272RightChunk000Certificate_eq_true
  unfold block272RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block272RightChunk000) (lo := block272RightChunk000L) (hi := block272RightChunk000R)
    (w1 := block272W1) (w2 := block272W2) (w3 := block272W3) (w4 := block272W4)
    (s1 := block272S1) (s2 := block272S2) (s3 := block272S3) (s4 := block272S4)
    hboxes hcover block272RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block272_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block272RightL : ℝ) (block272RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block272S1 : ℝ))
    (hy2ne : y ≠ (block272S2 : ℝ))
    (hy3ne : y ≠ (block272S3 : ℝ))
    (hy4ne : y ≠ (block272S4 : ℝ)) :
    0 < block272V y := by
  have hL : (block272RightChunk000L : ℝ) = (block272RightL : ℝ) := by
    norm_num [block272RightChunk000L, block272RightL]
  have hR : (block272RightChunk000R : ℝ) = (block272RightR : ℝ) := by
    norm_num [block272RightChunk000R, block272RightR]
  have hyc : y ∈ Icc (block272RightChunk000L : ℝ) (block272RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block272_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block272_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block272LeftL : ℝ) (block272LeftR : ℝ) →
    y ≠ 0 → y ≠ (block272S1 : ℝ) → y ≠ (block272S2 : ℝ) →
    y ≠ (block272S3 : ℝ) → y ≠ (block272S4 : ℝ) → 0 < block272V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block272RightL : ℝ) (block272RightR : ℝ) →
    y ≠ 0 → y ≠ (block272S1 : ℝ) → y ≠ (block272S2 : ℝ) →
    y ≠ (block272S3 : ℝ) → y ≠ (block272S4 : ℝ) → 0 < block272V y)

theorem block272_reallog_certificate_proof :
    block272_reallog_certificate := by
  exact ⟨block272_left_V_pos, block272_right_V_pos⟩

end Block272
end M1817475
end Erdos1038Lean
