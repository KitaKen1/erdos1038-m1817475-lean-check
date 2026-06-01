import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block367

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block367

open Set

def block367W1 : Rat := ((4364504206452013 : Rat) / 5000000000000000)
def block367W2 : Rat := ((23617266813961667 : Rat) / 500000000000000000)
def block367W3 : Rat := ((7703336001297899 : Rat) / 50000000000000000)
def block367W4 : Rat := ((6970803274157947 : Rat) / 50000000000000000)
def block367S1 : Rat := ((18174751 : Rat) / 10000000)
def block367S2 : Rat := ((511587 : Rat) / 200000)
def block367S3 : Rat := ((132959034910714285749 : Rat) / 50000000000000000000)
def block367S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block367V (y : ℝ) : ℝ :=
  ratPotential block367W1 block367W2 block367W3 block367W4 block367S1 block367S2 block367S3 block367S4 y

def block367LeftParamsCertificate : Bool :=
  allBoxesSameParams block367LeftBoxes block367W1 block367W2 block367W3 block367W4 block367S1 block367S2 block367S3 block367S4

theorem block367LeftParamsCertificate_eq_true :
    block367LeftParamsCertificate = true := by
  native_decide

theorem block367_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block367LeftL : ℝ) (block367LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block367S1 : ℝ))
    (hy2ne : y ≠ (block367S2 : ℝ))
    (hy3ne : y ≠ (block367S3 : ℝ))
    (hy4ne : y ≠ (block367S4 : ℝ)) :
    0 < block367V y := by
  have hcert := block367LeftCertificate_eq_true
  unfold block367LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block367LeftBoxes) (lo := block367LeftL) (hi := block367LeftR)
    (w1 := block367W1) (w2 := block367W2) (w3 := block367W3) (w4 := block367W4)
    (s1 := block367S1) (s2 := block367S2) (s3 := block367S3) (s4 := block367S4)
    hboxes hcover block367LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block367RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block367RightChunk000 block367W1 block367W2 block367W3 block367W4 block367S1 block367S2 block367S3 block367S4

theorem block367RightChunk000ParamsCertificate_eq_true :
    block367RightChunk000ParamsCertificate = true := by
  native_decide

theorem block367_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block367RightChunk000L : ℝ) (block367RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block367S1 : ℝ))
    (hy2ne : y ≠ (block367S2 : ℝ))
    (hy3ne : y ≠ (block367S3 : ℝ))
    (hy4ne : y ≠ (block367S4 : ℝ)) :
    0 < block367V y := by
  have hcert := block367RightChunk000Certificate_eq_true
  unfold block367RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block367RightChunk000) (lo := block367RightChunk000L) (hi := block367RightChunk000R)
    (w1 := block367W1) (w2 := block367W2) (w3 := block367W3) (w4 := block367W4)
    (s1 := block367S1) (s2 := block367S2) (s3 := block367S3) (s4 := block367S4)
    hboxes hcover block367RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block367_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block367RightL : ℝ) (block367RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block367S1 : ℝ))
    (hy2ne : y ≠ (block367S2 : ℝ))
    (hy3ne : y ≠ (block367S3 : ℝ))
    (hy4ne : y ≠ (block367S4 : ℝ)) :
    0 < block367V y := by
  have hL : (block367RightChunk000L : ℝ) = (block367RightL : ℝ) := by
    norm_num [block367RightChunk000L, block367RightL]
  have hR : (block367RightChunk000R : ℝ) = (block367RightR : ℝ) := by
    norm_num [block367RightChunk000R, block367RightR]
  have hyc : y ∈ Icc (block367RightChunk000L : ℝ) (block367RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block367_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block367_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block367LeftL : ℝ) (block367LeftR : ℝ) →
    y ≠ 0 → y ≠ (block367S1 : ℝ) → y ≠ (block367S2 : ℝ) →
    y ≠ (block367S3 : ℝ) → y ≠ (block367S4 : ℝ) → 0 < block367V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block367RightL : ℝ) (block367RightR : ℝ) →
    y ≠ 0 → y ≠ (block367S1 : ℝ) → y ≠ (block367S2 : ℝ) →
    y ≠ (block367S3 : ℝ) → y ≠ (block367S4 : ℝ) → 0 < block367V y)

theorem block367_reallog_certificate_proof :
    block367_reallog_certificate := by
  exact ⟨block367_left_V_pos, block367_right_V_pos⟩

end Block367
end M1817475
end Erdos1038Lean
