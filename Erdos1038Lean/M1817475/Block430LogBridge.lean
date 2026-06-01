import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block430

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block430

open Set

def block430W1 : Rat := ((52505170979413 : Rat) / 80000000000000)
def block430W2 : Rat := (0 : Rat)
def block430W3 : Rat := ((3079092225428003 : Rat) / 10000000000000000)
def block430W4 : Rat := ((797975540227693 : Rat) / 10000000000000000)
def block430S1 : Rat := ((18174751 : Rat) / 10000000)
def block430S2 : Rat := ((511587 : Rat) / 200000)
def block430S3 : Rat := ((131727441160714285803 : Rat) / 50000000000000000000)
def block430S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block430V (y : ℝ) : ℝ :=
  ratPotential block430W1 block430W2 block430W3 block430W4 block430S1 block430S2 block430S3 block430S4 y

def block430LeftParamsCertificate : Bool :=
  allBoxesSameParams block430LeftBoxes block430W1 block430W2 block430W3 block430W4 block430S1 block430S2 block430S3 block430S4

theorem block430LeftParamsCertificate_eq_true :
    block430LeftParamsCertificate = true := by
  native_decide

theorem block430_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block430LeftL : ℝ) (block430LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block430S1 : ℝ))
    (hy2ne : y ≠ (block430S2 : ℝ))
    (hy3ne : y ≠ (block430S3 : ℝ))
    (hy4ne : y ≠ (block430S4 : ℝ)) :
    0 < block430V y := by
  have hcert := block430LeftCertificate_eq_true
  unfold block430LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block430LeftBoxes) (lo := block430LeftL) (hi := block430LeftR)
    (w1 := block430W1) (w2 := block430W2) (w3 := block430W3) (w4 := block430W4)
    (s1 := block430S1) (s2 := block430S2) (s3 := block430S3) (s4 := block430S4)
    hboxes hcover block430LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block430RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block430RightChunk000 block430W1 block430W2 block430W3 block430W4 block430S1 block430S2 block430S3 block430S4

theorem block430RightChunk000ParamsCertificate_eq_true :
    block430RightChunk000ParamsCertificate = true := by
  native_decide

theorem block430_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block430RightChunk000L : ℝ) (block430RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block430S1 : ℝ))
    (hy2ne : y ≠ (block430S2 : ℝ))
    (hy3ne : y ≠ (block430S3 : ℝ))
    (hy4ne : y ≠ (block430S4 : ℝ)) :
    0 < block430V y := by
  have hcert := block430RightChunk000Certificate_eq_true
  unfold block430RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block430RightChunk000) (lo := block430RightChunk000L) (hi := block430RightChunk000R)
    (w1 := block430W1) (w2 := block430W2) (w3 := block430W3) (w4 := block430W4)
    (s1 := block430S1) (s2 := block430S2) (s3 := block430S3) (s4 := block430S4)
    hboxes hcover block430RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block430_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block430RightL : ℝ) (block430RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block430S1 : ℝ))
    (hy2ne : y ≠ (block430S2 : ℝ))
    (hy3ne : y ≠ (block430S3 : ℝ))
    (hy4ne : y ≠ (block430S4 : ℝ)) :
    0 < block430V y := by
  have hL : (block430RightChunk000L : ℝ) = (block430RightL : ℝ) := by
    norm_num [block430RightChunk000L, block430RightL]
  have hR : (block430RightChunk000R : ℝ) = (block430RightR : ℝ) := by
    norm_num [block430RightChunk000R, block430RightR]
  have hyc : y ∈ Icc (block430RightChunk000L : ℝ) (block430RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block430_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block430_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block430LeftL : ℝ) (block430LeftR : ℝ) →
    y ≠ 0 → y ≠ (block430S1 : ℝ) → y ≠ (block430S2 : ℝ) →
    y ≠ (block430S3 : ℝ) → y ≠ (block430S4 : ℝ) → 0 < block430V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block430RightL : ℝ) (block430RightR : ℝ) →
    y ≠ 0 → y ≠ (block430S1 : ℝ) → y ≠ (block430S2 : ℝ) →
    y ≠ (block430S3 : ℝ) → y ≠ (block430S4 : ℝ) → 0 < block430V y)

theorem block430_reallog_certificate_proof :
    block430_reallog_certificate := by
  exact ⟨block430_left_V_pos, block430_right_V_pos⟩

end Block430
end M1817475
end Erdos1038Lean
