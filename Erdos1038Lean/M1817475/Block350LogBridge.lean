import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block350

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block350

open Set

def block350W1 : Rat := ((9063165441676297 : Rat) / 10000000000000000)
def block350W2 : Rat := ((2377343432279637 : Rat) / 50000000000000000)
def block350W3 : Rat := ((1489142296114339 : Rat) / 10000000000000000)
def block350W4 : Rat := ((1382757398318953 : Rat) / 10000000000000000)
def block350S1 : Rat := ((18174751 : Rat) / 10000000)
def block350S2 : Rat := ((511587 : Rat) / 200000)
def block350S3 : Rat := ((133291369732142857163 : Rat) / 50000000000000000000)
def block350S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block350V (y : ℝ) : ℝ :=
  ratPotential block350W1 block350W2 block350W3 block350W4 block350S1 block350S2 block350S3 block350S4 y

def block350LeftParamsCertificate : Bool :=
  allBoxesSameParams block350LeftBoxes block350W1 block350W2 block350W3 block350W4 block350S1 block350S2 block350S3 block350S4

theorem block350LeftParamsCertificate_eq_true :
    block350LeftParamsCertificate = true := by
  native_decide

theorem block350_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block350LeftL : ℝ) (block350LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block350S1 : ℝ))
    (hy2ne : y ≠ (block350S2 : ℝ))
    (hy3ne : y ≠ (block350S3 : ℝ))
    (hy4ne : y ≠ (block350S4 : ℝ)) :
    0 < block350V y := by
  have hcert := block350LeftCertificate_eq_true
  unfold block350LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block350LeftBoxes) (lo := block350LeftL) (hi := block350LeftR)
    (w1 := block350W1) (w2 := block350W2) (w3 := block350W3) (w4 := block350W4)
    (s1 := block350S1) (s2 := block350S2) (s3 := block350S3) (s4 := block350S4)
    hboxes hcover block350LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block350RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block350RightChunk000 block350W1 block350W2 block350W3 block350W4 block350S1 block350S2 block350S3 block350S4

theorem block350RightChunk000ParamsCertificate_eq_true :
    block350RightChunk000ParamsCertificate = true := by
  native_decide

theorem block350_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block350RightChunk000L : ℝ) (block350RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block350S1 : ℝ))
    (hy2ne : y ≠ (block350S2 : ℝ))
    (hy3ne : y ≠ (block350S3 : ℝ))
    (hy4ne : y ≠ (block350S4 : ℝ)) :
    0 < block350V y := by
  have hcert := block350RightChunk000Certificate_eq_true
  unfold block350RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block350RightChunk000) (lo := block350RightChunk000L) (hi := block350RightChunk000R)
    (w1 := block350W1) (w2 := block350W2) (w3 := block350W3) (w4 := block350W4)
    (s1 := block350S1) (s2 := block350S2) (s3 := block350S3) (s4 := block350S4)
    hboxes hcover block350RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block350_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block350RightL : ℝ) (block350RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block350S1 : ℝ))
    (hy2ne : y ≠ (block350S2 : ℝ))
    (hy3ne : y ≠ (block350S3 : ℝ))
    (hy4ne : y ≠ (block350S4 : ℝ)) :
    0 < block350V y := by
  have hL : (block350RightChunk000L : ℝ) = (block350RightL : ℝ) := by
    norm_num [block350RightChunk000L, block350RightL]
  have hR : (block350RightChunk000R : ℝ) = (block350RightR : ℝ) := by
    norm_num [block350RightChunk000R, block350RightR]
  have hyc : y ∈ Icc (block350RightChunk000L : ℝ) (block350RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block350_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block350_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block350LeftL : ℝ) (block350LeftR : ℝ) →
    y ≠ 0 → y ≠ (block350S1 : ℝ) → y ≠ (block350S2 : ℝ) →
    y ≠ (block350S3 : ℝ) → y ≠ (block350S4 : ℝ) → 0 < block350V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block350RightL : ℝ) (block350RightR : ℝ) →
    y ≠ 0 → y ≠ (block350S1 : ℝ) → y ≠ (block350S2 : ℝ) →
    y ≠ (block350S3 : ℝ) → y ≠ (block350S4 : ℝ) → 0 < block350V y)

theorem block350_reallog_certificate_proof :
    block350_reallog_certificate := by
  exact ⟨block350_left_V_pos, block350_right_V_pos⟩

end Block350
end M1817475
end Erdos1038Lean
