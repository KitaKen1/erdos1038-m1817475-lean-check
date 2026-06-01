import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block330

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block330

open Set

def block330W1 : Rat := ((9498486707815261 : Rat) / 10000000000000000)
def block330W2 : Rat := ((1179365044608273 : Rat) / 25000000000000000)
def block330W3 : Rat := ((7166933576613979 : Rat) / 50000000000000000)
def block330W4 : Rat := ((2736970013854167 : Rat) / 20000000000000000)
def block330S1 : Rat := ((18174751 : Rat) / 10000000)
def block330S2 : Rat := ((511587 : Rat) / 200000)
def block330S3 : Rat := ((133682351875000000003 : Rat) / 50000000000000000000)
def block330S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block330V (y : ℝ) : ℝ :=
  ratPotential block330W1 block330W2 block330W3 block330W4 block330S1 block330S2 block330S3 block330S4 y

def block330LeftParamsCertificate : Bool :=
  allBoxesSameParams block330LeftBoxes block330W1 block330W2 block330W3 block330W4 block330S1 block330S2 block330S3 block330S4

theorem block330LeftParamsCertificate_eq_true :
    block330LeftParamsCertificate = true := by
  native_decide

theorem block330_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block330LeftL : ℝ) (block330LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block330S1 : ℝ))
    (hy2ne : y ≠ (block330S2 : ℝ))
    (hy3ne : y ≠ (block330S3 : ℝ))
    (hy4ne : y ≠ (block330S4 : ℝ)) :
    0 < block330V y := by
  have hcert := block330LeftCertificate_eq_true
  unfold block330LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block330LeftBoxes) (lo := block330LeftL) (hi := block330LeftR)
    (w1 := block330W1) (w2 := block330W2) (w3 := block330W3) (w4 := block330W4)
    (s1 := block330S1) (s2 := block330S2) (s3 := block330S3) (s4 := block330S4)
    hboxes hcover block330LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block330RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block330RightChunk000 block330W1 block330W2 block330W3 block330W4 block330S1 block330S2 block330S3 block330S4

theorem block330RightChunk000ParamsCertificate_eq_true :
    block330RightChunk000ParamsCertificate = true := by
  native_decide

theorem block330_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block330RightChunk000L : ℝ) (block330RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block330S1 : ℝ))
    (hy2ne : y ≠ (block330S2 : ℝ))
    (hy3ne : y ≠ (block330S3 : ℝ))
    (hy4ne : y ≠ (block330S4 : ℝ)) :
    0 < block330V y := by
  have hcert := block330RightChunk000Certificate_eq_true
  unfold block330RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block330RightChunk000) (lo := block330RightChunk000L) (hi := block330RightChunk000R)
    (w1 := block330W1) (w2 := block330W2) (w3 := block330W3) (w4 := block330W4)
    (s1 := block330S1) (s2 := block330S2) (s3 := block330S3) (s4 := block330S4)
    hboxes hcover block330RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block330_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block330RightL : ℝ) (block330RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block330S1 : ℝ))
    (hy2ne : y ≠ (block330S2 : ℝ))
    (hy3ne : y ≠ (block330S3 : ℝ))
    (hy4ne : y ≠ (block330S4 : ℝ)) :
    0 < block330V y := by
  have hL : (block330RightChunk000L : ℝ) = (block330RightL : ℝ) := by
    norm_num [block330RightChunk000L, block330RightL]
  have hR : (block330RightChunk000R : ℝ) = (block330RightR : ℝ) := by
    norm_num [block330RightChunk000R, block330RightR]
  have hyc : y ∈ Icc (block330RightChunk000L : ℝ) (block330RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block330_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block330_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block330LeftL : ℝ) (block330LeftR : ℝ) →
    y ≠ 0 → y ≠ (block330S1 : ℝ) → y ≠ (block330S2 : ℝ) →
    y ≠ (block330S3 : ℝ) → y ≠ (block330S4 : ℝ) → 0 < block330V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block330RightL : ℝ) (block330RightR : ℝ) →
    y ≠ 0 → y ≠ (block330S1 : ℝ) → y ≠ (block330S2 : ℝ) →
    y ≠ (block330S3 : ℝ) → y ≠ (block330S4 : ℝ) → 0 < block330V y)

theorem block330_reallog_certificate_proof :
    block330_reallog_certificate := by
  exact ⟨block330_left_V_pos, block330_right_V_pos⟩

end Block330
end M1817475
end Erdos1038Lean
