import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block337

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block337

open Set

def block337W1 : Rat := ((583864449938457 : Rat) / 625000000000000)
def block337W2 : Rat := ((23697123752953627 : Rat) / 500000000000000000)
def block337W3 : Rat := ((453582220245449 : Rat) / 3125000000000000)
def block337W4 : Rat := ((274857657627737 : Rat) / 2000000000000000)
def block337S1 : Rat := ((18174751 : Rat) / 10000000)
def block337S2 : Rat := ((511587 : Rat) / 200000)
def block337S3 : Rat := ((133545508125000000009 : Rat) / 50000000000000000000)
def block337S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block337V (y : ℝ) : ℝ :=
  ratPotential block337W1 block337W2 block337W3 block337W4 block337S1 block337S2 block337S3 block337S4 y

def block337LeftParamsCertificate : Bool :=
  allBoxesSameParams block337LeftBoxes block337W1 block337W2 block337W3 block337W4 block337S1 block337S2 block337S3 block337S4

theorem block337LeftParamsCertificate_eq_true :
    block337LeftParamsCertificate = true := by
  native_decide

theorem block337_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block337LeftL : ℝ) (block337LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block337S1 : ℝ))
    (hy2ne : y ≠ (block337S2 : ℝ))
    (hy3ne : y ≠ (block337S3 : ℝ))
    (hy4ne : y ≠ (block337S4 : ℝ)) :
    0 < block337V y := by
  have hcert := block337LeftCertificate_eq_true
  unfold block337LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block337LeftBoxes) (lo := block337LeftL) (hi := block337LeftR)
    (w1 := block337W1) (w2 := block337W2) (w3 := block337W3) (w4 := block337W4)
    (s1 := block337S1) (s2 := block337S2) (s3 := block337S3) (s4 := block337S4)
    hboxes hcover block337LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block337RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block337RightChunk000 block337W1 block337W2 block337W3 block337W4 block337S1 block337S2 block337S3 block337S4

theorem block337RightChunk000ParamsCertificate_eq_true :
    block337RightChunk000ParamsCertificate = true := by
  native_decide

theorem block337_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block337RightChunk000L : ℝ) (block337RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block337S1 : ℝ))
    (hy2ne : y ≠ (block337S2 : ℝ))
    (hy3ne : y ≠ (block337S3 : ℝ))
    (hy4ne : y ≠ (block337S4 : ℝ)) :
    0 < block337V y := by
  have hcert := block337RightChunk000Certificate_eq_true
  unfold block337RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block337RightChunk000) (lo := block337RightChunk000L) (hi := block337RightChunk000R)
    (w1 := block337W1) (w2 := block337W2) (w3 := block337W3) (w4 := block337W4)
    (s1 := block337S1) (s2 := block337S2) (s3 := block337S3) (s4 := block337S4)
    hboxes hcover block337RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block337_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block337RightL : ℝ) (block337RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block337S1 : ℝ))
    (hy2ne : y ≠ (block337S2 : ℝ))
    (hy3ne : y ≠ (block337S3 : ℝ))
    (hy4ne : y ≠ (block337S4 : ℝ)) :
    0 < block337V y := by
  have hL : (block337RightChunk000L : ℝ) = (block337RightL : ℝ) := by
    norm_num [block337RightChunk000L, block337RightL]
  have hR : (block337RightChunk000R : ℝ) = (block337RightR : ℝ) := by
    norm_num [block337RightChunk000R, block337RightR]
  have hyc : y ∈ Icc (block337RightChunk000L : ℝ) (block337RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block337_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block337_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block337LeftL : ℝ) (block337LeftR : ℝ) →
    y ≠ 0 → y ≠ (block337S1 : ℝ) → y ≠ (block337S2 : ℝ) →
    y ≠ (block337S3 : ℝ) → y ≠ (block337S4 : ℝ) → 0 < block337V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block337RightL : ℝ) (block337RightR : ℝ) →
    y ≠ 0 → y ≠ (block337S1 : ℝ) → y ≠ (block337S2 : ℝ) →
    y ≠ (block337S3 : ℝ) → y ≠ (block337S4 : ℝ) → 0 < block337V y)

theorem block337_reallog_certificate_proof :
    block337_reallog_certificate := by
  exact ⟨block337_left_V_pos, block337_right_V_pos⟩

end Block337
end M1817475
end Erdos1038Lean
