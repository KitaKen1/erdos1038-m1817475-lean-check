import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block347

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block347

open Set

def block347W1 : Rat := ((9126515935711021 : Rat) / 10000000000000000)
def block347W2 : Rat := ((23776835148960583 : Rat) / 500000000000000000)
def block347W3 : Rat := ((2958861279122817 : Rat) / 20000000000000000)
def block347W4 : Rat := ((3453552535021493 : Rat) / 25000000000000000)
def block347S1 : Rat := ((18174751 : Rat) / 10000000)
def block347S2 : Rat := ((511587 : Rat) / 200000)
def block347S3 : Rat := ((133350017053571428589 : Rat) / 50000000000000000000)
def block347S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block347V (y : ℝ) : ℝ :=
  ratPotential block347W1 block347W2 block347W3 block347W4 block347S1 block347S2 block347S3 block347S4 y

def block347LeftParamsCertificate : Bool :=
  allBoxesSameParams block347LeftBoxes block347W1 block347W2 block347W3 block347W4 block347S1 block347S2 block347S3 block347S4

theorem block347LeftParamsCertificate_eq_true :
    block347LeftParamsCertificate = true := by
  native_decide

theorem block347_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block347LeftL : ℝ) (block347LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block347S1 : ℝ))
    (hy2ne : y ≠ (block347S2 : ℝ))
    (hy3ne : y ≠ (block347S3 : ℝ))
    (hy4ne : y ≠ (block347S4 : ℝ)) :
    0 < block347V y := by
  have hcert := block347LeftCertificate_eq_true
  unfold block347LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block347LeftBoxes) (lo := block347LeftL) (hi := block347LeftR)
    (w1 := block347W1) (w2 := block347W2) (w3 := block347W3) (w4 := block347W4)
    (s1 := block347S1) (s2 := block347S2) (s3 := block347S3) (s4 := block347S4)
    hboxes hcover block347LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block347RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block347RightChunk000 block347W1 block347W2 block347W3 block347W4 block347S1 block347S2 block347S3 block347S4

theorem block347RightChunk000ParamsCertificate_eq_true :
    block347RightChunk000ParamsCertificate = true := by
  native_decide

theorem block347_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block347RightChunk000L : ℝ) (block347RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block347S1 : ℝ))
    (hy2ne : y ≠ (block347S2 : ℝ))
    (hy3ne : y ≠ (block347S3 : ℝ))
    (hy4ne : y ≠ (block347S4 : ℝ)) :
    0 < block347V y := by
  have hcert := block347RightChunk000Certificate_eq_true
  unfold block347RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block347RightChunk000) (lo := block347RightChunk000L) (hi := block347RightChunk000R)
    (w1 := block347W1) (w2 := block347W2) (w3 := block347W3) (w4 := block347W4)
    (s1 := block347S1) (s2 := block347S2) (s3 := block347S3) (s4 := block347S4)
    hboxes hcover block347RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block347_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block347RightL : ℝ) (block347RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block347S1 : ℝ))
    (hy2ne : y ≠ (block347S2 : ℝ))
    (hy3ne : y ≠ (block347S3 : ℝ))
    (hy4ne : y ≠ (block347S4 : ℝ)) :
    0 < block347V y := by
  have hL : (block347RightChunk000L : ℝ) = (block347RightL : ℝ) := by
    norm_num [block347RightChunk000L, block347RightL]
  have hR : (block347RightChunk000R : ℝ) = (block347RightR : ℝ) := by
    norm_num [block347RightChunk000R, block347RightR]
  have hyc : y ∈ Icc (block347RightChunk000L : ℝ) (block347RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block347_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block347_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block347LeftL : ℝ) (block347LeftR : ℝ) →
    y ≠ 0 → y ≠ (block347S1 : ℝ) → y ≠ (block347S2 : ℝ) →
    y ≠ (block347S3 : ℝ) → y ≠ (block347S4 : ℝ) → 0 < block347V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block347RightL : ℝ) (block347RightR : ℝ) →
    y ≠ 0 → y ≠ (block347S1 : ℝ) → y ≠ (block347S2 : ℝ) →
    y ≠ (block347S3 : ℝ) → y ≠ (block347S4 : ℝ) → 0 < block347V y)

theorem block347_reallog_certificate_proof :
    block347_reallog_certificate := by
  exact ⟨block347_left_V_pos, block347_right_V_pos⟩

end Block347
end M1817475
end Erdos1038Lean
