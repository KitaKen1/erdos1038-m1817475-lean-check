import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block438

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block438

open Set

def block438W1 : Rat := ((3162124581093727 : Rat) / 5000000000000000)
def block438W2 : Rat := (0 : Rat)
def block438W3 : Rat := ((31750014430623763 : Rat) / 100000000000000000)
def block438W4 : Rat := ((3755545879992561 : Rat) / 50000000000000000)
def block438S1 : Rat := ((18174751 : Rat) / 10000000)
def block438S2 : Rat := ((511587 : Rat) / 200000)
def block438S3 : Rat := ((131571048303571428667 : Rat) / 50000000000000000000)
def block438S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block438V (y : ℝ) : ℝ :=
  ratPotential block438W1 block438W2 block438W3 block438W4 block438S1 block438S2 block438S3 block438S4 y

def block438LeftParamsCertificate : Bool :=
  allBoxesSameParams block438LeftBoxes block438W1 block438W2 block438W3 block438W4 block438S1 block438S2 block438S3 block438S4

theorem block438LeftParamsCertificate_eq_true :
    block438LeftParamsCertificate = true := by
  native_decide

theorem block438_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block438LeftL : ℝ) (block438LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block438S1 : ℝ))
    (hy2ne : y ≠ (block438S2 : ℝ))
    (hy3ne : y ≠ (block438S3 : ℝ))
    (hy4ne : y ≠ (block438S4 : ℝ)) :
    0 < block438V y := by
  have hcert := block438LeftCertificate_eq_true
  unfold block438LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block438LeftBoxes) (lo := block438LeftL) (hi := block438LeftR)
    (w1 := block438W1) (w2 := block438W2) (w3 := block438W3) (w4 := block438W4)
    (s1 := block438S1) (s2 := block438S2) (s3 := block438S3) (s4 := block438S4)
    hboxes hcover block438LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block438RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block438RightChunk000 block438W1 block438W2 block438W3 block438W4 block438S1 block438S2 block438S3 block438S4

theorem block438RightChunk000ParamsCertificate_eq_true :
    block438RightChunk000ParamsCertificate = true := by
  native_decide

theorem block438_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block438RightChunk000L : ℝ) (block438RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block438S1 : ℝ))
    (hy2ne : y ≠ (block438S2 : ℝ))
    (hy3ne : y ≠ (block438S3 : ℝ))
    (hy4ne : y ≠ (block438S4 : ℝ)) :
    0 < block438V y := by
  have hcert := block438RightChunk000Certificate_eq_true
  unfold block438RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block438RightChunk000) (lo := block438RightChunk000L) (hi := block438RightChunk000R)
    (w1 := block438W1) (w2 := block438W2) (w3 := block438W3) (w4 := block438W4)
    (s1 := block438S1) (s2 := block438S2) (s3 := block438S3) (s4 := block438S4)
    hboxes hcover block438RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block438_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block438RightL : ℝ) (block438RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block438S1 : ℝ))
    (hy2ne : y ≠ (block438S2 : ℝ))
    (hy3ne : y ≠ (block438S3 : ℝ))
    (hy4ne : y ≠ (block438S4 : ℝ)) :
    0 < block438V y := by
  have hL : (block438RightChunk000L : ℝ) = (block438RightL : ℝ) := by
    norm_num [block438RightChunk000L, block438RightL]
  have hR : (block438RightChunk000R : ℝ) = (block438RightR : ℝ) := by
    norm_num [block438RightChunk000R, block438RightR]
  have hyc : y ∈ Icc (block438RightChunk000L : ℝ) (block438RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block438_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block438_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block438LeftL : ℝ) (block438LeftR : ℝ) →
    y ≠ 0 → y ≠ (block438S1 : ℝ) → y ≠ (block438S2 : ℝ) →
    y ≠ (block438S3 : ℝ) → y ≠ (block438S4 : ℝ) → 0 < block438V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block438RightL : ℝ) (block438RightR : ℝ) →
    y ≠ 0 → y ≠ (block438S1 : ℝ) → y ≠ (block438S2 : ℝ) →
    y ≠ (block438S3 : ℝ) → y ≠ (block438S4 : ℝ) → 0 < block438V y)

theorem block438_reallog_certificate_proof :
    block438_reallog_certificate := by
  exact ⟨block438_left_V_pos, block438_right_V_pos⟩

end Block438
end M1817475
end Erdos1038Lean
