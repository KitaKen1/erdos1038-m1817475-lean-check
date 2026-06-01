import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block349

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block349

open Set

def block349W1 : Rat := ((1816500300933297 : Rat) / 2000000000000000)
def block349W2 : Rat := ((5949247682841493 : Rat) / 125000000000000000)
def block349W3 : Rat := ((7428468025484497 : Rat) / 50000000000000000)
def block349W4 : Rat := ((3455732069190453 : Rat) / 25000000000000000)
def block349S1 : Rat := ((18174751 : Rat) / 10000000)
def block349S2 : Rat := ((511587 : Rat) / 200000)
def block349S3 : Rat := ((26662183767857142861 : Rat) / 10000000000000000000)
def block349S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block349V (y : ℝ) : ℝ :=
  ratPotential block349W1 block349W2 block349W3 block349W4 block349S1 block349S2 block349S3 block349S4 y

def block349LeftParamsCertificate : Bool :=
  allBoxesSameParams block349LeftBoxes block349W1 block349W2 block349W3 block349W4 block349S1 block349S2 block349S3 block349S4

theorem block349LeftParamsCertificate_eq_true :
    block349LeftParamsCertificate = true := by
  native_decide

theorem block349_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block349LeftL : ℝ) (block349LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block349S1 : ℝ))
    (hy2ne : y ≠ (block349S2 : ℝ))
    (hy3ne : y ≠ (block349S3 : ℝ))
    (hy4ne : y ≠ (block349S4 : ℝ)) :
    0 < block349V y := by
  have hcert := block349LeftCertificate_eq_true
  unfold block349LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block349LeftBoxes) (lo := block349LeftL) (hi := block349LeftR)
    (w1 := block349W1) (w2 := block349W2) (w3 := block349W3) (w4 := block349W4)
    (s1 := block349S1) (s2 := block349S2) (s3 := block349S3) (s4 := block349S4)
    hboxes hcover block349LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block349RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block349RightChunk000 block349W1 block349W2 block349W3 block349W4 block349S1 block349S2 block349S3 block349S4

theorem block349RightChunk000ParamsCertificate_eq_true :
    block349RightChunk000ParamsCertificate = true := by
  native_decide

theorem block349_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block349RightChunk000L : ℝ) (block349RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block349S1 : ℝ))
    (hy2ne : y ≠ (block349S2 : ℝ))
    (hy3ne : y ≠ (block349S3 : ℝ))
    (hy4ne : y ≠ (block349S4 : ℝ)) :
    0 < block349V y := by
  have hcert := block349RightChunk000Certificate_eq_true
  unfold block349RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block349RightChunk000) (lo := block349RightChunk000L) (hi := block349RightChunk000R)
    (w1 := block349W1) (w2 := block349W2) (w3 := block349W3) (w4 := block349W4)
    (s1 := block349S1) (s2 := block349S2) (s3 := block349S3) (s4 := block349S4)
    hboxes hcover block349RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block349_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block349RightL : ℝ) (block349RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block349S1 : ℝ))
    (hy2ne : y ≠ (block349S2 : ℝ))
    (hy3ne : y ≠ (block349S3 : ℝ))
    (hy4ne : y ≠ (block349S4 : ℝ)) :
    0 < block349V y := by
  have hL : (block349RightChunk000L : ℝ) = (block349RightL : ℝ) := by
    norm_num [block349RightChunk000L, block349RightL]
  have hR : (block349RightChunk000R : ℝ) = (block349RightR : ℝ) := by
    norm_num [block349RightChunk000R, block349RightR]
  have hyc : y ∈ Icc (block349RightChunk000L : ℝ) (block349RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block349_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block349_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block349LeftL : ℝ) (block349LeftR : ℝ) →
    y ≠ 0 → y ≠ (block349S1 : ℝ) → y ≠ (block349S2 : ℝ) →
    y ≠ (block349S3 : ℝ) → y ≠ (block349S4 : ℝ) → 0 < block349V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block349RightL : ℝ) (block349RightR : ℝ) →
    y ≠ 0 → y ≠ (block349S1 : ℝ) → y ≠ (block349S2 : ℝ) →
    y ≠ (block349S3 : ℝ) → y ≠ (block349S4 : ℝ) → 0 < block349V y)

theorem block349_reallog_certificate_proof :
    block349_reallog_certificate := by
  exact ⟨block349_left_V_pos, block349_right_V_pos⟩

end Block349
end M1817475
end Erdos1038Lean
