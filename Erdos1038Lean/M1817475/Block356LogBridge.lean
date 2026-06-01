import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block356

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block356

open Set

def block356W1 : Rat := ((4471729879892043 : Rat) / 5000000000000000)
def block356W2 : Rat := ((11858715346994909 : Rat) / 250000000000000000)
def block356W3 : Rat := ((1884664832942853 : Rat) / 12500000000000000)
def block356W4 : Rat := ((13864719119000987 : Rat) / 100000000000000000)
def block356S1 : Rat := ((18174751 : Rat) / 10000000)
def block356S2 : Rat := ((511587 : Rat) / 200000)
def block356S3 : Rat := ((133174075089285714311 : Rat) / 50000000000000000000)
def block356S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block356V (y : ℝ) : ℝ :=
  ratPotential block356W1 block356W2 block356W3 block356W4 block356S1 block356S2 block356S3 block356S4 y

def block356LeftParamsCertificate : Bool :=
  allBoxesSameParams block356LeftBoxes block356W1 block356W2 block356W3 block356W4 block356S1 block356S2 block356S3 block356S4

theorem block356LeftParamsCertificate_eq_true :
    block356LeftParamsCertificate = true := by
  native_decide

theorem block356_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block356LeftL : ℝ) (block356LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block356S1 : ℝ))
    (hy2ne : y ≠ (block356S2 : ℝ))
    (hy3ne : y ≠ (block356S3 : ℝ))
    (hy4ne : y ≠ (block356S4 : ℝ)) :
    0 < block356V y := by
  have hcert := block356LeftCertificate_eq_true
  unfold block356LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block356LeftBoxes) (lo := block356LeftL) (hi := block356LeftR)
    (w1 := block356W1) (w2 := block356W2) (w3 := block356W3) (w4 := block356W4)
    (s1 := block356S1) (s2 := block356S2) (s3 := block356S3) (s4 := block356S4)
    hboxes hcover block356LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block356RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block356RightChunk000 block356W1 block356W2 block356W3 block356W4 block356S1 block356S2 block356S3 block356S4

theorem block356RightChunk000ParamsCertificate_eq_true :
    block356RightChunk000ParamsCertificate = true := by
  native_decide

theorem block356_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block356RightChunk000L : ℝ) (block356RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block356S1 : ℝ))
    (hy2ne : y ≠ (block356S2 : ℝ))
    (hy3ne : y ≠ (block356S3 : ℝ))
    (hy4ne : y ≠ (block356S4 : ℝ)) :
    0 < block356V y := by
  have hcert := block356RightChunk000Certificate_eq_true
  unfold block356RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block356RightChunk000) (lo := block356RightChunk000L) (hi := block356RightChunk000R)
    (w1 := block356W1) (w2 := block356W2) (w3 := block356W3) (w4 := block356W4)
    (s1 := block356S1) (s2 := block356S2) (s3 := block356S3) (s4 := block356S4)
    hboxes hcover block356RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block356_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block356RightL : ℝ) (block356RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block356S1 : ℝ))
    (hy2ne : y ≠ (block356S2 : ℝ))
    (hy3ne : y ≠ (block356S3 : ℝ))
    (hy4ne : y ≠ (block356S4 : ℝ)) :
    0 < block356V y := by
  have hL : (block356RightChunk000L : ℝ) = (block356RightL : ℝ) := by
    norm_num [block356RightChunk000L, block356RightL]
  have hR : (block356RightChunk000R : ℝ) = (block356RightR : ℝ) := by
    norm_num [block356RightChunk000R, block356RightR]
  have hyc : y ∈ Icc (block356RightChunk000L : ℝ) (block356RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block356_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block356_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block356LeftL : ℝ) (block356LeftR : ℝ) →
    y ≠ 0 → y ≠ (block356S1 : ℝ) → y ≠ (block356S2 : ℝ) →
    y ≠ (block356S3 : ℝ) → y ≠ (block356S4 : ℝ) → 0 < block356V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block356RightL : ℝ) (block356RightR : ℝ) →
    y ≠ 0 → y ≠ (block356S1 : ℝ) → y ≠ (block356S2 : ℝ) →
    y ≠ (block356S3 : ℝ) → y ≠ (block356S4 : ℝ) → 0 < block356V y)

theorem block356_reallog_certificate_proof :
    block356_reallog_certificate := by
  exact ⟨block356_left_V_pos, block356_right_V_pos⟩

end Block356
end M1817475
end Erdos1038Lean
