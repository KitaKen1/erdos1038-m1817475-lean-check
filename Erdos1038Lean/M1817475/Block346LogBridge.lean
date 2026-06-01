import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block346

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block346

open Set

def block346W1 : Rat := ((2286488682802317 : Rat) / 2500000000000000)
def block346W2 : Rat := ((4759328815458273 : Rat) / 100000000000000000)
def block346W3 : Rat := ((461307160432129 : Rat) / 3125000000000000)
def block346W4 : Rat := ((2761670293116919 : Rat) / 20000000000000000)
def block346S1 : Rat := ((18174751 : Rat) / 10000000)
def block346S2 : Rat := ((511587 : Rat) / 200000)
def block346S3 : Rat := ((133369566160714285731 : Rat) / 50000000000000000000)
def block346S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block346V (y : ℝ) : ℝ :=
  ratPotential block346W1 block346W2 block346W3 block346W4 block346S1 block346S2 block346S3 block346S4 y

def block346LeftParamsCertificate : Bool :=
  allBoxesSameParams block346LeftBoxes block346W1 block346W2 block346W3 block346W4 block346S1 block346S2 block346S3 block346S4

theorem block346LeftParamsCertificate_eq_true :
    block346LeftParamsCertificate = true := by
  native_decide

theorem block346_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block346LeftL : ℝ) (block346LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block346S1 : ℝ))
    (hy2ne : y ≠ (block346S2 : ℝ))
    (hy3ne : y ≠ (block346S3 : ℝ))
    (hy4ne : y ≠ (block346S4 : ℝ)) :
    0 < block346V y := by
  have hcert := block346LeftCertificate_eq_true
  unfold block346LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block346LeftBoxes) (lo := block346LeftL) (hi := block346LeftR)
    (w1 := block346W1) (w2 := block346W2) (w3 := block346W3) (w4 := block346W4)
    (s1 := block346S1) (s2 := block346S2) (s3 := block346S3) (s4 := block346S4)
    hboxes hcover block346LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block346RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block346RightChunk000 block346W1 block346W2 block346W3 block346W4 block346S1 block346S2 block346S3 block346S4

theorem block346RightChunk000ParamsCertificate_eq_true :
    block346RightChunk000ParamsCertificate = true := by
  native_decide

theorem block346_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block346RightChunk000L : ℝ) (block346RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block346S1 : ℝ))
    (hy2ne : y ≠ (block346S2 : ℝ))
    (hy3ne : y ≠ (block346S3 : ℝ))
    (hy4ne : y ≠ (block346S4 : ℝ)) :
    0 < block346V y := by
  have hcert := block346RightChunk000Certificate_eq_true
  unfold block346RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block346RightChunk000) (lo := block346RightChunk000L) (hi := block346RightChunk000R)
    (w1 := block346W1) (w2 := block346W2) (w3 := block346W3) (w4 := block346W4)
    (s1 := block346S1) (s2 := block346S2) (s3 := block346S3) (s4 := block346S4)
    hboxes hcover block346RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block346_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block346RightL : ℝ) (block346RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block346S1 : ℝ))
    (hy2ne : y ≠ (block346S2 : ℝ))
    (hy3ne : y ≠ (block346S3 : ℝ))
    (hy4ne : y ≠ (block346S4 : ℝ)) :
    0 < block346V y := by
  have hL : (block346RightChunk000L : ℝ) = (block346RightL : ℝ) := by
    norm_num [block346RightChunk000L, block346RightL]
  have hR : (block346RightChunk000R : ℝ) = (block346RightR : ℝ) := by
    norm_num [block346RightChunk000R, block346RightR]
  have hyc : y ∈ Icc (block346RightChunk000L : ℝ) (block346RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block346_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block346_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block346LeftL : ℝ) (block346LeftR : ℝ) →
    y ≠ 0 → y ≠ (block346S1 : ℝ) → y ≠ (block346S2 : ℝ) →
    y ≠ (block346S3 : ℝ) → y ≠ (block346S4 : ℝ) → 0 < block346V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block346RightL : ℝ) (block346RightR : ℝ) →
    y ≠ 0 → y ≠ (block346S1 : ℝ) → y ≠ (block346S2 : ℝ) →
    y ≠ (block346S3 : ℝ) → y ≠ (block346S4 : ℝ) → 0 < block346V y)

theorem block346_reallog_certificate_proof :
    block346_reallog_certificate := by
  exact ⟨block346_left_V_pos, block346_right_V_pos⟩

end Block346
end M1817475
end Erdos1038Lean
