import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block151

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block151

open Set

def block151W1 : Rat := ((1081072152223641 : Rat) / 500000000000000)
def block151W2 : Rat := (0 : Rat)
def block151W3 : Rat := ((678351110898479 : Rat) / 4000000000000000)
def block151W4 : Rat := ((83193584364351 : Rat) / 1000000000000000)
def block151S1 : Rat := ((18174751 : Rat) / 10000000)
def block151S2 : Rat := ((511587 : Rat) / 200000)
def block151S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block151S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block151V (y : ℝ) : ℝ :=
  ratPotential block151W1 block151W2 block151W3 block151W4 block151S1 block151S2 block151S3 block151S4 y

def block151LeftParamsCertificate : Bool :=
  allBoxesSameParams block151LeftBoxes block151W1 block151W2 block151W3 block151W4 block151S1 block151S2 block151S3 block151S4

theorem block151LeftParamsCertificate_eq_true :
    block151LeftParamsCertificate = true := by
  native_decide

theorem block151_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block151LeftL : ℝ) (block151LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block151S1 : ℝ))
    (hy2ne : y ≠ (block151S2 : ℝ))
    (hy3ne : y ≠ (block151S3 : ℝ))
    (hy4ne : y ≠ (block151S4 : ℝ)) :
    0 < block151V y := by
  have hcert := block151LeftCertificate_eq_true
  unfold block151LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block151LeftBoxes) (lo := block151LeftL) (hi := block151LeftR)
    (w1 := block151W1) (w2 := block151W2) (w3 := block151W3) (w4 := block151W4)
    (s1 := block151S1) (s2 := block151S2) (s3 := block151S3) (s4 := block151S4)
    hboxes hcover block151LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block151RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block151RightChunk000 block151W1 block151W2 block151W3 block151W4 block151S1 block151S2 block151S3 block151S4

theorem block151RightChunk000ParamsCertificate_eq_true :
    block151RightChunk000ParamsCertificate = true := by
  native_decide

theorem block151_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block151RightChunk000L : ℝ) (block151RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block151S1 : ℝ))
    (hy2ne : y ≠ (block151S2 : ℝ))
    (hy3ne : y ≠ (block151S3 : ℝ))
    (hy4ne : y ≠ (block151S4 : ℝ)) :
    0 < block151V y := by
  have hcert := block151RightChunk000Certificate_eq_true
  unfold block151RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block151RightChunk000) (lo := block151RightChunk000L) (hi := block151RightChunk000R)
    (w1 := block151W1) (w2 := block151W2) (w3 := block151W3) (w4 := block151W4)
    (s1 := block151S1) (s2 := block151S2) (s3 := block151S3) (s4 := block151S4)
    hboxes hcover block151RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block151_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block151RightL : ℝ) (block151RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block151S1 : ℝ))
    (hy2ne : y ≠ (block151S2 : ℝ))
    (hy3ne : y ≠ (block151S3 : ℝ))
    (hy4ne : y ≠ (block151S4 : ℝ)) :
    0 < block151V y := by
  have hL : (block151RightChunk000L : ℝ) = (block151RightL : ℝ) := by
    norm_num [block151RightChunk000L, block151RightL]
  have hR : (block151RightChunk000R : ℝ) = (block151RightR : ℝ) := by
    norm_num [block151RightChunk000R, block151RightR]
  have hyc : y ∈ Icc (block151RightChunk000L : ℝ) (block151RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block151_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block151_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block151LeftL : ℝ) (block151LeftR : ℝ) →
    y ≠ 0 → y ≠ (block151S1 : ℝ) → y ≠ (block151S2 : ℝ) →
    y ≠ (block151S3 : ℝ) → y ≠ (block151S4 : ℝ) → 0 < block151V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block151RightL : ℝ) (block151RightR : ℝ) →
    y ≠ 0 → y ≠ (block151S1 : ℝ) → y ≠ (block151S2 : ℝ) →
    y ≠ (block151S3 : ℝ) → y ≠ (block151S4 : ℝ) → 0 < block151V y)

theorem block151_reallog_certificate_proof :
    block151_reallog_certificate := by
  exact ⟨block151_left_V_pos, block151_right_V_pos⟩

end Block151
end M1817475
end Erdos1038Lean
