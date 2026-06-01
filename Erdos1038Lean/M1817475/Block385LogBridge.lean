import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block385

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block385

open Set

def block385W1 : Rat := ((2103091039420947 : Rat) / 2500000000000000)
def block385W2 : Rat := ((4607077689151067 : Rat) / 100000000000000000)
def block385W3 : Rat := ((499833304295811 : Rat) / 3125000000000000)
def block385W4 : Rat := ((14068533329876967 : Rat) / 100000000000000000)
def block385S1 : Rat := ((18174751 : Rat) / 10000000)
def block385S2 : Rat := ((511587 : Rat) / 200000)
def block385S3 : Rat := ((132607150982142857193 : Rat) / 50000000000000000000)
def block385S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block385V (y : ℝ) : ℝ :=
  ratPotential block385W1 block385W2 block385W3 block385W4 block385S1 block385S2 block385S3 block385S4 y

def block385LeftParamsCertificate : Bool :=
  allBoxesSameParams block385LeftBoxes block385W1 block385W2 block385W3 block385W4 block385S1 block385S2 block385S3 block385S4

theorem block385LeftParamsCertificate_eq_true :
    block385LeftParamsCertificate = true := by
  native_decide

theorem block385_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block385LeftL : ℝ) (block385LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block385S1 : ℝ))
    (hy2ne : y ≠ (block385S2 : ℝ))
    (hy3ne : y ≠ (block385S3 : ℝ))
    (hy4ne : y ≠ (block385S4 : ℝ)) :
    0 < block385V y := by
  have hcert := block385LeftCertificate_eq_true
  unfold block385LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block385LeftBoxes) (lo := block385LeftL) (hi := block385LeftR)
    (w1 := block385W1) (w2 := block385W2) (w3 := block385W3) (w4 := block385W4)
    (s1 := block385S1) (s2 := block385S2) (s3 := block385S3) (s4 := block385S4)
    hboxes hcover block385LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block385RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block385RightChunk000 block385W1 block385W2 block385W3 block385W4 block385S1 block385S2 block385S3 block385S4

theorem block385RightChunk000ParamsCertificate_eq_true :
    block385RightChunk000ParamsCertificate = true := by
  native_decide

theorem block385_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block385RightChunk000L : ℝ) (block385RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block385S1 : ℝ))
    (hy2ne : y ≠ (block385S2 : ℝ))
    (hy3ne : y ≠ (block385S3 : ℝ))
    (hy4ne : y ≠ (block385S4 : ℝ)) :
    0 < block385V y := by
  have hcert := block385RightChunk000Certificate_eq_true
  unfold block385RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block385RightChunk000) (lo := block385RightChunk000L) (hi := block385RightChunk000R)
    (w1 := block385W1) (w2 := block385W2) (w3 := block385W3) (w4 := block385W4)
    (s1 := block385S1) (s2 := block385S2) (s3 := block385S3) (s4 := block385S4)
    hboxes hcover block385RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block385_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block385RightL : ℝ) (block385RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block385S1 : ℝ))
    (hy2ne : y ≠ (block385S2 : ℝ))
    (hy3ne : y ≠ (block385S3 : ℝ))
    (hy4ne : y ≠ (block385S4 : ℝ)) :
    0 < block385V y := by
  have hL : (block385RightChunk000L : ℝ) = (block385RightL : ℝ) := by
    norm_num [block385RightChunk000L, block385RightL]
  have hR : (block385RightChunk000R : ℝ) = (block385RightR : ℝ) := by
    norm_num [block385RightChunk000R, block385RightR]
  have hyc : y ∈ Icc (block385RightChunk000L : ℝ) (block385RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block385_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block385_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block385LeftL : ℝ) (block385LeftR : ℝ) →
    y ≠ 0 → y ≠ (block385S1 : ℝ) → y ≠ (block385S2 : ℝ) →
    y ≠ (block385S3 : ℝ) → y ≠ (block385S4 : ℝ) → 0 < block385V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block385RightL : ℝ) (block385RightR : ℝ) →
    y ≠ 0 → y ≠ (block385S1 : ℝ) → y ≠ (block385S2 : ℝ) →
    y ≠ (block385S3 : ℝ) → y ≠ (block385S4 : ℝ) → 0 < block385V y)

theorem block385_reallog_certificate_proof :
    block385_reallog_certificate := by
  exact ⟨block385_left_V_pos, block385_right_V_pos⟩

end Block385
end M1817475
end Erdos1038Lean
