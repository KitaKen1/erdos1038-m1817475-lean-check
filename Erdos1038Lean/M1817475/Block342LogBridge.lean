import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block342

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block342

open Set

def block342W1 : Rat := ((4616865644311689 : Rat) / 5000000000000000)
def block342W2 : Rat := ((23697723134774303 : Rat) / 500000000000000000)
def block342W3 : Rat := ((917237953025429 : Rat) / 6250000000000000)
def block342W4 : Rat := ((1376535112591559 : Rat) / 10000000000000000)
def block342S1 : Rat := ((18174751 : Rat) / 10000000)
def block342S2 : Rat := ((511587 : Rat) / 200000)
def block342S3 : Rat := ((133447762589285714299 : Rat) / 50000000000000000000)
def block342S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block342V (y : ℝ) : ℝ :=
  ratPotential block342W1 block342W2 block342W3 block342W4 block342S1 block342S2 block342S3 block342S4 y

def block342LeftParamsCertificate : Bool :=
  allBoxesSameParams block342LeftBoxes block342W1 block342W2 block342W3 block342W4 block342S1 block342S2 block342S3 block342S4

theorem block342LeftParamsCertificate_eq_true :
    block342LeftParamsCertificate = true := by
  native_decide

theorem block342_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block342LeftL : ℝ) (block342LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block342S1 : ℝ))
    (hy2ne : y ≠ (block342S2 : ℝ))
    (hy3ne : y ≠ (block342S3 : ℝ))
    (hy4ne : y ≠ (block342S4 : ℝ)) :
    0 < block342V y := by
  have hcert := block342LeftCertificate_eq_true
  unfold block342LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block342LeftBoxes) (lo := block342LeftL) (hi := block342LeftR)
    (w1 := block342W1) (w2 := block342W2) (w3 := block342W3) (w4 := block342W4)
    (s1 := block342S1) (s2 := block342S2) (s3 := block342S3) (s4 := block342S4)
    hboxes hcover block342LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block342RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block342RightChunk000 block342W1 block342W2 block342W3 block342W4 block342S1 block342S2 block342S3 block342S4

theorem block342RightChunk000ParamsCertificate_eq_true :
    block342RightChunk000ParamsCertificate = true := by
  native_decide

theorem block342_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block342RightChunk000L : ℝ) (block342RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block342S1 : ℝ))
    (hy2ne : y ≠ (block342S2 : ℝ))
    (hy3ne : y ≠ (block342S3 : ℝ))
    (hy4ne : y ≠ (block342S4 : ℝ)) :
    0 < block342V y := by
  have hcert := block342RightChunk000Certificate_eq_true
  unfold block342RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block342RightChunk000) (lo := block342RightChunk000L) (hi := block342RightChunk000R)
    (w1 := block342W1) (w2 := block342W2) (w3 := block342W3) (w4 := block342W4)
    (s1 := block342S1) (s2 := block342S2) (s3 := block342S3) (s4 := block342S4)
    hboxes hcover block342RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block342_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block342RightL : ℝ) (block342RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block342S1 : ℝ))
    (hy2ne : y ≠ (block342S2 : ℝ))
    (hy3ne : y ≠ (block342S3 : ℝ))
    (hy4ne : y ≠ (block342S4 : ℝ)) :
    0 < block342V y := by
  have hL : (block342RightChunk000L : ℝ) = (block342RightL : ℝ) := by
    norm_num [block342RightChunk000L, block342RightL]
  have hR : (block342RightChunk000R : ℝ) = (block342RightR : ℝ) := by
    norm_num [block342RightChunk000R, block342RightR]
  have hyc : y ∈ Icc (block342RightChunk000L : ℝ) (block342RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block342_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block342_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block342LeftL : ℝ) (block342LeftR : ℝ) →
    y ≠ 0 → y ≠ (block342S1 : ℝ) → y ≠ (block342S2 : ℝ) →
    y ≠ (block342S3 : ℝ) → y ≠ (block342S4 : ℝ) → 0 < block342V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block342RightL : ℝ) (block342RightR : ℝ) →
    y ≠ 0 → y ≠ (block342S1 : ℝ) → y ≠ (block342S2 : ℝ) →
    y ≠ (block342S3 : ℝ) → y ≠ (block342S4 : ℝ) → 0 < block342V y)

theorem block342_reallog_certificate_proof :
    block342_reallog_certificate := by
  exact ⟨block342_left_V_pos, block342_right_V_pos⟩

end Block342
end M1817475
end Erdos1038Lean
