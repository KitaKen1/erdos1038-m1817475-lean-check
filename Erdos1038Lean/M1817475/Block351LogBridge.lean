import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block351

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block351

open Set

def block351W1 : Rat := ((2260965466407353 : Rat) / 2500000000000000)
def block351W2 : Rat := ((474969059704461 : Rat) / 10000000000000000)
def block351W3 : Rat := ((3731653577735903 : Rat) / 25000000000000000)
def block351W4 : Rat := ((1383181308032081 : Rat) / 10000000000000000)
def block351S1 : Rat := ((18174751 : Rat) / 10000000)
def block351S2 : Rat := ((511587 : Rat) / 200000)
def block351S3 : Rat := ((133271820625000000021 : Rat) / 50000000000000000000)
def block351S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block351V (y : ℝ) : ℝ :=
  ratPotential block351W1 block351W2 block351W3 block351W4 block351S1 block351S2 block351S3 block351S4 y

def block351LeftParamsCertificate : Bool :=
  allBoxesSameParams block351LeftBoxes block351W1 block351W2 block351W3 block351W4 block351S1 block351S2 block351S3 block351S4

theorem block351LeftParamsCertificate_eq_true :
    block351LeftParamsCertificate = true := by
  native_decide

theorem block351_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block351LeftL : ℝ) (block351LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block351S1 : ℝ))
    (hy2ne : y ≠ (block351S2 : ℝ))
    (hy3ne : y ≠ (block351S3 : ℝ))
    (hy4ne : y ≠ (block351S4 : ℝ)) :
    0 < block351V y := by
  have hcert := block351LeftCertificate_eq_true
  unfold block351LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block351LeftBoxes) (lo := block351LeftL) (hi := block351LeftR)
    (w1 := block351W1) (w2 := block351W2) (w3 := block351W3) (w4 := block351W4)
    (s1 := block351S1) (s2 := block351S2) (s3 := block351S3) (s4 := block351S4)
    hboxes hcover block351LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block351RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block351RightChunk000 block351W1 block351W2 block351W3 block351W4 block351S1 block351S2 block351S3 block351S4

theorem block351RightChunk000ParamsCertificate_eq_true :
    block351RightChunk000ParamsCertificate = true := by
  native_decide

theorem block351_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block351RightChunk000L : ℝ) (block351RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block351S1 : ℝ))
    (hy2ne : y ≠ (block351S2 : ℝ))
    (hy3ne : y ≠ (block351S3 : ℝ))
    (hy4ne : y ≠ (block351S4 : ℝ)) :
    0 < block351V y := by
  have hcert := block351RightChunk000Certificate_eq_true
  unfold block351RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block351RightChunk000) (lo := block351RightChunk000L) (hi := block351RightChunk000R)
    (w1 := block351W1) (w2 := block351W2) (w3 := block351W3) (w4 := block351W4)
    (s1 := block351S1) (s2 := block351S2) (s3 := block351S3) (s4 := block351S4)
    hboxes hcover block351RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block351_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block351RightL : ℝ) (block351RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block351S1 : ℝ))
    (hy2ne : y ≠ (block351S2 : ℝ))
    (hy3ne : y ≠ (block351S3 : ℝ))
    (hy4ne : y ≠ (block351S4 : ℝ)) :
    0 < block351V y := by
  have hL : (block351RightChunk000L : ℝ) = (block351RightL : ℝ) := by
    norm_num [block351RightChunk000L, block351RightL]
  have hR : (block351RightChunk000R : ℝ) = (block351RightR : ℝ) := by
    norm_num [block351RightChunk000R, block351RightR]
  have hyc : y ∈ Icc (block351RightChunk000L : ℝ) (block351RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block351_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block351_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block351LeftL : ℝ) (block351LeftR : ℝ) →
    y ≠ 0 → y ≠ (block351S1 : ℝ) → y ≠ (block351S2 : ℝ) →
    y ≠ (block351S3 : ℝ) → y ≠ (block351S4 : ℝ) → 0 < block351V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block351RightL : ℝ) (block351RightR : ℝ) →
    y ≠ 0 → y ≠ (block351S1 : ℝ) → y ≠ (block351S2 : ℝ) →
    y ≠ (block351S3 : ℝ) → y ≠ (block351S4 : ℝ) → 0 < block351V y)

theorem block351_reallog_certificate_proof :
    block351_reallog_certificate := by
  exact ⟨block351_left_V_pos, block351_right_V_pos⟩

end Block351
end M1817475
end Erdos1038Lean
