import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block136

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block136

open Set

def block136W1 : Rat := ((12656420552943717 : Rat) / 5000000000000000)
def block136W2 : Rat := (0 : Rat)
def block136W3 : Rat := ((144329778721287 : Rat) / 1250000000000000)
def block136W4 : Rat := ((6236743580839603 : Rat) / 50000000000000000)
def block136S1 : Rat := ((18174751 : Rat) / 10000000)
def block136S2 : Rat := ((511587 : Rat) / 200000)
def block136S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block136S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block136V (y : ℝ) : ℝ :=
  ratPotential block136W1 block136W2 block136W3 block136W4 block136S1 block136S2 block136S3 block136S4 y

def block136LeftParamsCertificate : Bool :=
  allBoxesSameParams block136LeftBoxes block136W1 block136W2 block136W3 block136W4 block136S1 block136S2 block136S3 block136S4

theorem block136LeftParamsCertificate_eq_true :
    block136LeftParamsCertificate = true := by
  native_decide

theorem block136_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block136LeftL : ℝ) (block136LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block136S1 : ℝ))
    (hy2ne : y ≠ (block136S2 : ℝ))
    (hy3ne : y ≠ (block136S3 : ℝ))
    (hy4ne : y ≠ (block136S4 : ℝ)) :
    0 < block136V y := by
  have hcert := block136LeftCertificate_eq_true
  unfold block136LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block136LeftBoxes) (lo := block136LeftL) (hi := block136LeftR)
    (w1 := block136W1) (w2 := block136W2) (w3 := block136W3) (w4 := block136W4)
    (s1 := block136S1) (s2 := block136S2) (s3 := block136S3) (s4 := block136S4)
    hboxes hcover block136LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block136RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block136RightChunk000 block136W1 block136W2 block136W3 block136W4 block136S1 block136S2 block136S3 block136S4

theorem block136RightChunk000ParamsCertificate_eq_true :
    block136RightChunk000ParamsCertificate = true := by
  native_decide

theorem block136_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block136RightChunk000L : ℝ) (block136RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block136S1 : ℝ))
    (hy2ne : y ≠ (block136S2 : ℝ))
    (hy3ne : y ≠ (block136S3 : ℝ))
    (hy4ne : y ≠ (block136S4 : ℝ)) :
    0 < block136V y := by
  have hcert := block136RightChunk000Certificate_eq_true
  unfold block136RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block136RightChunk000) (lo := block136RightChunk000L) (hi := block136RightChunk000R)
    (w1 := block136W1) (w2 := block136W2) (w3 := block136W3) (w4 := block136W4)
    (s1 := block136S1) (s2 := block136S2) (s3 := block136S3) (s4 := block136S4)
    hboxes hcover block136RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block136_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block136RightL : ℝ) (block136RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block136S1 : ℝ))
    (hy2ne : y ≠ (block136S2 : ℝ))
    (hy3ne : y ≠ (block136S3 : ℝ))
    (hy4ne : y ≠ (block136S4 : ℝ)) :
    0 < block136V y := by
  have hL : (block136RightChunk000L : ℝ) = (block136RightL : ℝ) := by
    norm_num [block136RightChunk000L, block136RightL]
  have hR : (block136RightChunk000R : ℝ) = (block136RightR : ℝ) := by
    norm_num [block136RightChunk000R, block136RightR]
  have hyc : y ∈ Icc (block136RightChunk000L : ℝ) (block136RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block136_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block136_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block136LeftL : ℝ) (block136LeftR : ℝ) →
    y ≠ 0 → y ≠ (block136S1 : ℝ) → y ≠ (block136S2 : ℝ) →
    y ≠ (block136S3 : ℝ) → y ≠ (block136S4 : ℝ) → 0 < block136V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block136RightL : ℝ) (block136RightR : ℝ) →
    y ≠ 0 → y ≠ (block136S1 : ℝ) → y ≠ (block136S2 : ℝ) →
    y ≠ (block136S3 : ℝ) → y ≠ (block136S4 : ℝ) → 0 < block136V y)

theorem block136_reallog_certificate_proof :
    block136_reallog_certificate := by
  exact ⟨block136_left_V_pos, block136_right_V_pos⟩

end Block136
end M1817475
end Erdos1038Lean
