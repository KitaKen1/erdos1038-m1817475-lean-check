import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block002

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block002

open Set

def block002W1 : Rat := ((13945984790705499 : Rat) / 1000000000000000)
def block002W2 : Rat := (0 : Rat)
def block002W3 : Rat := (0 : Rat)
def block002W4 : Rat := ((2483882062574517 : Rat) / 10000000000000000)
def block002S1 : Rat := ((18174751 : Rat) / 10000000)
def block002S2 : Rat := ((511587 : Rat) / 200000)
def block002S3 : Rat := ((107000619 : Rat) / 40000000)
def block002S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block002V (y : ℝ) : ℝ :=
  ratPotential block002W1 block002W2 block002W3 block002W4 block002S1 block002S2 block002S3 block002S4 y

def block002LeftParamsCertificate : Bool :=
  allBoxesSameParams block002LeftBoxes block002W1 block002W2 block002W3 block002W4 block002S1 block002S2 block002S3 block002S4

theorem block002LeftParamsCertificate_eq_true :
    block002LeftParamsCertificate = true := by
  native_decide

theorem block002_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block002LeftL : ℝ) (block002LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block002S1 : ℝ))
    (hy2ne : y ≠ (block002S2 : ℝ))
    (hy3ne : y ≠ (block002S3 : ℝ))
    (hy4ne : y ≠ (block002S4 : ℝ)) :
    0 < block002V y := by
  have hcert := block002LeftCertificate_eq_true
  unfold block002LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block002LeftBoxes) (lo := block002LeftL) (hi := block002LeftR)
    (w1 := block002W1) (w2 := block002W2) (w3 := block002W3) (w4 := block002W4)
    (s1 := block002S1) (s2 := block002S2) (s3 := block002S3) (s4 := block002S4)
    hboxes hcover block002LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block002RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block002RightChunk000 block002W1 block002W2 block002W3 block002W4 block002S1 block002S2 block002S3 block002S4

theorem block002RightChunk000ParamsCertificate_eq_true :
    block002RightChunk000ParamsCertificate = true := by
  native_decide

theorem block002_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block002RightChunk000L : ℝ) (block002RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block002S1 : ℝ))
    (hy2ne : y ≠ (block002S2 : ℝ))
    (hy3ne : y ≠ (block002S3 : ℝ))
    (hy4ne : y ≠ (block002S4 : ℝ)) :
    0 < block002V y := by
  have hcert := block002RightChunk000Certificate_eq_true
  unfold block002RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block002RightChunk000) (lo := block002RightChunk000L) (hi := block002RightChunk000R)
    (w1 := block002W1) (w2 := block002W2) (w3 := block002W3) (w4 := block002W4)
    (s1 := block002S1) (s2 := block002S2) (s3 := block002S3) (s4 := block002S4)
    hboxes hcover block002RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block002_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block002RightL : ℝ) (block002RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block002S1 : ℝ))
    (hy2ne : y ≠ (block002S2 : ℝ))
    (hy3ne : y ≠ (block002S3 : ℝ))
    (hy4ne : y ≠ (block002S4 : ℝ)) :
    0 < block002V y := by
  have hL : (block002RightChunk000L : ℝ) = (block002RightL : ℝ) := by
    norm_num [block002RightChunk000L, block002RightL]
  have hR : (block002RightChunk000R : ℝ) = (block002RightR : ℝ) := by
    norm_num [block002RightChunk000R, block002RightR]
  have hyc : y ∈ Icc (block002RightChunk000L : ℝ) (block002RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block002_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block002_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block002LeftL : ℝ) (block002LeftR : ℝ) →
    y ≠ 0 → y ≠ (block002S1 : ℝ) → y ≠ (block002S2 : ℝ) →
    y ≠ (block002S3 : ℝ) → y ≠ (block002S4 : ℝ) → 0 < block002V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block002RightL : ℝ) (block002RightR : ℝ) →
    y ≠ 0 → y ≠ (block002S1 : ℝ) → y ≠ (block002S2 : ℝ) →
    y ≠ (block002S3 : ℝ) → y ≠ (block002S4 : ℝ) → 0 < block002V y)

theorem block002_reallog_certificate_proof :
    block002_reallog_certificate := by
  exact ⟨block002_left_V_pos, block002_right_V_pos⟩

end Block002
end M1817475
end Erdos1038Lean
