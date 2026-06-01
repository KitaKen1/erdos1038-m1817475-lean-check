import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block353

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block353

open Set

def block353W1 : Rat := ((2250262504208217 : Rat) / 2500000000000000)
def block353W2 : Rat := ((4761155216780289 : Rat) / 100000000000000000)
def block353W3 : Rat := ((3741075219411287 : Rat) / 25000000000000000)
def block353W4 : Rat := ((692824335890697 : Rat) / 5000000000000000)
def block353S1 : Rat := ((18174751 : Rat) / 10000000)
def block353S2 : Rat := ((511587 : Rat) / 200000)
def block353S3 : Rat := ((133232722410714285737 : Rat) / 50000000000000000000)
def block353S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block353V (y : ℝ) : ℝ :=
  ratPotential block353W1 block353W2 block353W3 block353W4 block353S1 block353S2 block353S3 block353S4 y

def block353LeftParamsCertificate : Bool :=
  allBoxesSameParams block353LeftBoxes block353W1 block353W2 block353W3 block353W4 block353S1 block353S2 block353S3 block353S4

theorem block353LeftParamsCertificate_eq_true :
    block353LeftParamsCertificate = true := by
  native_decide

theorem block353_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block353LeftL : ℝ) (block353LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block353S1 : ℝ))
    (hy2ne : y ≠ (block353S2 : ℝ))
    (hy3ne : y ≠ (block353S3 : ℝ))
    (hy4ne : y ≠ (block353S4 : ℝ)) :
    0 < block353V y := by
  have hcert := block353LeftCertificate_eq_true
  unfold block353LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block353LeftBoxes) (lo := block353LeftL) (hi := block353LeftR)
    (w1 := block353W1) (w2 := block353W2) (w3 := block353W3) (w4 := block353W4)
    (s1 := block353S1) (s2 := block353S2) (s3 := block353S3) (s4 := block353S4)
    hboxes hcover block353LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block353RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block353RightChunk000 block353W1 block353W2 block353W3 block353W4 block353S1 block353S2 block353S3 block353S4

theorem block353RightChunk000ParamsCertificate_eq_true :
    block353RightChunk000ParamsCertificate = true := by
  native_decide

theorem block353_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block353RightChunk000L : ℝ) (block353RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block353S1 : ℝ))
    (hy2ne : y ≠ (block353S2 : ℝ))
    (hy3ne : y ≠ (block353S3 : ℝ))
    (hy4ne : y ≠ (block353S4 : ℝ)) :
    0 < block353V y := by
  have hcert := block353RightChunk000Certificate_eq_true
  unfold block353RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block353RightChunk000) (lo := block353RightChunk000L) (hi := block353RightChunk000R)
    (w1 := block353W1) (w2 := block353W2) (w3 := block353W3) (w4 := block353W4)
    (s1 := block353S1) (s2 := block353S2) (s3 := block353S3) (s4 := block353S4)
    hboxes hcover block353RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block353_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block353RightL : ℝ) (block353RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block353S1 : ℝ))
    (hy2ne : y ≠ (block353S2 : ℝ))
    (hy3ne : y ≠ (block353S3 : ℝ))
    (hy4ne : y ≠ (block353S4 : ℝ)) :
    0 < block353V y := by
  have hL : (block353RightChunk000L : ℝ) = (block353RightL : ℝ) := by
    norm_num [block353RightChunk000L, block353RightL]
  have hR : (block353RightChunk000R : ℝ) = (block353RightR : ℝ) := by
    norm_num [block353RightChunk000R, block353RightR]
  have hyc : y ∈ Icc (block353RightChunk000L : ℝ) (block353RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block353_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block353_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block353LeftL : ℝ) (block353LeftR : ℝ) →
    y ≠ 0 → y ≠ (block353S1 : ℝ) → y ≠ (block353S2 : ℝ) →
    y ≠ (block353S3 : ℝ) → y ≠ (block353S4 : ℝ) → 0 < block353V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block353RightL : ℝ) (block353RightR : ℝ) →
    y ≠ 0 → y ≠ (block353S1 : ℝ) → y ≠ (block353S2 : ℝ) →
    y ≠ (block353S3 : ℝ) → y ≠ (block353S4 : ℝ) → 0 < block353V y)

theorem block353_reallog_certificate_proof :
    block353_reallog_certificate := by
  exact ⟨block353_left_V_pos, block353_right_V_pos⟩

end Block353
end M1817475
end Erdos1038Lean
