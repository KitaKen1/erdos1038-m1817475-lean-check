import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block379

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block379

open Set

def block379W1 : Rat := ((68102128982591 : Rat) / 80000000000000)
def block379W2 : Rat := ((2919689326872981 : Rat) / 62500000000000000)
def block379W3 : Rat := ((1970474055792517 : Rat) / 12500000000000000)
def block379W4 : Rat := ((280809037636893 : Rat) / 2000000000000000)
def block379S1 : Rat := ((18174751 : Rat) / 10000000)
def block379S2 : Rat := ((511587 : Rat) / 200000)
def block379S3 : Rat := ((26544889125000000009 : Rat) / 10000000000000000000)
def block379S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block379V (y : ℝ) : ℝ :=
  ratPotential block379W1 block379W2 block379W3 block379W4 block379S1 block379S2 block379S3 block379S4 y

def block379LeftParamsCertificate : Bool :=
  allBoxesSameParams block379LeftBoxes block379W1 block379W2 block379W3 block379W4 block379S1 block379S2 block379S3 block379S4

theorem block379LeftParamsCertificate_eq_true :
    block379LeftParamsCertificate = true := by
  native_decide

theorem block379_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block379LeftL : ℝ) (block379LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block379S1 : ℝ))
    (hy2ne : y ≠ (block379S2 : ℝ))
    (hy3ne : y ≠ (block379S3 : ℝ))
    (hy4ne : y ≠ (block379S4 : ℝ)) :
    0 < block379V y := by
  have hcert := block379LeftCertificate_eq_true
  unfold block379LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block379LeftBoxes) (lo := block379LeftL) (hi := block379LeftR)
    (w1 := block379W1) (w2 := block379W2) (w3 := block379W3) (w4 := block379W4)
    (s1 := block379S1) (s2 := block379S2) (s3 := block379S3) (s4 := block379S4)
    hboxes hcover block379LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block379RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block379RightChunk000 block379W1 block379W2 block379W3 block379W4 block379S1 block379S2 block379S3 block379S4

theorem block379RightChunk000ParamsCertificate_eq_true :
    block379RightChunk000ParamsCertificate = true := by
  native_decide

theorem block379_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block379RightChunk000L : ℝ) (block379RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block379S1 : ℝ))
    (hy2ne : y ≠ (block379S2 : ℝ))
    (hy3ne : y ≠ (block379S3 : ℝ))
    (hy4ne : y ≠ (block379S4 : ℝ)) :
    0 < block379V y := by
  have hcert := block379RightChunk000Certificate_eq_true
  unfold block379RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block379RightChunk000) (lo := block379RightChunk000L) (hi := block379RightChunk000R)
    (w1 := block379W1) (w2 := block379W2) (w3 := block379W3) (w4 := block379W4)
    (s1 := block379S1) (s2 := block379S2) (s3 := block379S3) (s4 := block379S4)
    hboxes hcover block379RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block379_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block379RightL : ℝ) (block379RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block379S1 : ℝ))
    (hy2ne : y ≠ (block379S2 : ℝ))
    (hy3ne : y ≠ (block379S3 : ℝ))
    (hy4ne : y ≠ (block379S4 : ℝ)) :
    0 < block379V y := by
  have hL : (block379RightChunk000L : ℝ) = (block379RightL : ℝ) := by
    norm_num [block379RightChunk000L, block379RightL]
  have hR : (block379RightChunk000R : ℝ) = (block379RightR : ℝ) := by
    norm_num [block379RightChunk000R, block379RightR]
  have hyc : y ∈ Icc (block379RightChunk000L : ℝ) (block379RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block379_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block379_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block379LeftL : ℝ) (block379LeftR : ℝ) →
    y ≠ 0 → y ≠ (block379S1 : ℝ) → y ≠ (block379S2 : ℝ) →
    y ≠ (block379S3 : ℝ) → y ≠ (block379S4 : ℝ) → 0 < block379V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block379RightL : ℝ) (block379RightR : ℝ) →
    y ≠ 0 → y ≠ (block379S1 : ℝ) → y ≠ (block379S2 : ℝ) →
    y ≠ (block379S3 : ℝ) → y ≠ (block379S4 : ℝ) → 0 < block379V y)

theorem block379_reallog_certificate_proof :
    block379_reallog_certificate := by
  exact ⟨block379_left_V_pos, block379_right_V_pos⟩

end Block379
end M1817475
end Erdos1038Lean
