import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block334

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block334

open Set

def block334W1 : Rat := ((9406379247491681 : Rat) / 10000000000000000)
def block334W2 : Rat := ((1478878507543403 : Rat) / 31250000000000000)
def block334W3 : Rat := ((225677179191981 : Rat) / 1562500000000000)
def block334W4 : Rat := ((548495405908633 : Rat) / 4000000000000000)
def block334S1 : Rat := ((18174751 : Rat) / 10000000)
def block334S2 : Rat := ((511587 : Rat) / 200000)
def block334S3 : Rat := ((26720831089285714287 : Rat) / 10000000000000000000)
def block334S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block334V (y : ℝ) : ℝ :=
  ratPotential block334W1 block334W2 block334W3 block334W4 block334S1 block334S2 block334S3 block334S4 y

def block334LeftParamsCertificate : Bool :=
  allBoxesSameParams block334LeftBoxes block334W1 block334W2 block334W3 block334W4 block334S1 block334S2 block334S3 block334S4

theorem block334LeftParamsCertificate_eq_true :
    block334LeftParamsCertificate = true := by
  native_decide

theorem block334_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block334LeftL : ℝ) (block334LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block334S1 : ℝ))
    (hy2ne : y ≠ (block334S2 : ℝ))
    (hy3ne : y ≠ (block334S3 : ℝ))
    (hy4ne : y ≠ (block334S4 : ℝ)) :
    0 < block334V y := by
  have hcert := block334LeftCertificate_eq_true
  unfold block334LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block334LeftBoxes) (lo := block334LeftL) (hi := block334LeftR)
    (w1 := block334W1) (w2 := block334W2) (w3 := block334W3) (w4 := block334W4)
    (s1 := block334S1) (s2 := block334S2) (s3 := block334S3) (s4 := block334S4)
    hboxes hcover block334LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block334RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block334RightChunk000 block334W1 block334W2 block334W3 block334W4 block334S1 block334S2 block334S3 block334S4

theorem block334RightChunk000ParamsCertificate_eq_true :
    block334RightChunk000ParamsCertificate = true := by
  native_decide

theorem block334_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block334RightChunk000L : ℝ) (block334RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block334S1 : ℝ))
    (hy2ne : y ≠ (block334S2 : ℝ))
    (hy3ne : y ≠ (block334S3 : ℝ))
    (hy4ne : y ≠ (block334S4 : ℝ)) :
    0 < block334V y := by
  have hcert := block334RightChunk000Certificate_eq_true
  unfold block334RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block334RightChunk000) (lo := block334RightChunk000L) (hi := block334RightChunk000R)
    (w1 := block334W1) (w2 := block334W2) (w3 := block334W3) (w4 := block334W4)
    (s1 := block334S1) (s2 := block334S2) (s3 := block334S3) (s4 := block334S4)
    hboxes hcover block334RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block334_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block334RightL : ℝ) (block334RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block334S1 : ℝ))
    (hy2ne : y ≠ (block334S2 : ℝ))
    (hy3ne : y ≠ (block334S3 : ℝ))
    (hy4ne : y ≠ (block334S4 : ℝ)) :
    0 < block334V y := by
  have hL : (block334RightChunk000L : ℝ) = (block334RightL : ℝ) := by
    norm_num [block334RightChunk000L, block334RightL]
  have hR : (block334RightChunk000R : ℝ) = (block334RightR : ℝ) := by
    norm_num [block334RightChunk000R, block334RightR]
  have hyc : y ∈ Icc (block334RightChunk000L : ℝ) (block334RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block334_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block334_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block334LeftL : ℝ) (block334LeftR : ℝ) →
    y ≠ 0 → y ≠ (block334S1 : ℝ) → y ≠ (block334S2 : ℝ) →
    y ≠ (block334S3 : ℝ) → y ≠ (block334S4 : ℝ) → 0 < block334V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block334RightL : ℝ) (block334RightR : ℝ) →
    y ≠ 0 → y ≠ (block334S1 : ℝ) → y ≠ (block334S2 : ℝ) →
    y ≠ (block334S3 : ℝ) → y ≠ (block334S4 : ℝ) → 0 < block334V y)

theorem block334_reallog_certificate_proof :
    block334_reallog_certificate := by
  exact ⟨block334_left_V_pos, block334_right_V_pos⟩

end Block334
end M1817475
end Erdos1038Lean
