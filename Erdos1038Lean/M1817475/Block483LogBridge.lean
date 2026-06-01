import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block483

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block483

open Set

def block483W1 : Rat := ((3165283946993 : Rat) / 6250000000000)
def block483W2 : Rat := (0 : Rat)
def block483W3 : Rat := ((38335410318535373 : Rat) / 100000000000000000)
def block483W4 : Rat := ((7801318811834529 : Rat) / 200000000000000000)
def block483S1 : Rat := ((18174751 : Rat) / 10000000)
def block483S2 : Rat := ((511587 : Rat) / 200000)
def block483S3 : Rat := ((130691338482142857277 : Rat) / 50000000000000000000)
def block483S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block483V (y : ℝ) : ℝ :=
  ratPotential block483W1 block483W2 block483W3 block483W4 block483S1 block483S2 block483S3 block483S4 y

def block483LeftParamsCertificate : Bool :=
  allBoxesSameParams block483LeftBoxes block483W1 block483W2 block483W3 block483W4 block483S1 block483S2 block483S3 block483S4

theorem block483LeftParamsCertificate_eq_true :
    block483LeftParamsCertificate = true := by
  native_decide

theorem block483_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block483LeftL : ℝ) (block483LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block483S1 : ℝ))
    (hy2ne : y ≠ (block483S2 : ℝ))
    (hy3ne : y ≠ (block483S3 : ℝ))
    (hy4ne : y ≠ (block483S4 : ℝ)) :
    0 < block483V y := by
  have hcert := block483LeftCertificate_eq_true
  unfold block483LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block483LeftBoxes) (lo := block483LeftL) (hi := block483LeftR)
    (w1 := block483W1) (w2 := block483W2) (w3 := block483W3) (w4 := block483W4)
    (s1 := block483S1) (s2 := block483S2) (s3 := block483S3) (s4 := block483S4)
    hboxes hcover block483LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block483RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block483RightChunk000 block483W1 block483W2 block483W3 block483W4 block483S1 block483S2 block483S3 block483S4

theorem block483RightChunk000ParamsCertificate_eq_true :
    block483RightChunk000ParamsCertificate = true := by
  native_decide

theorem block483_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block483RightChunk000L : ℝ) (block483RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block483S1 : ℝ))
    (hy2ne : y ≠ (block483S2 : ℝ))
    (hy3ne : y ≠ (block483S3 : ℝ))
    (hy4ne : y ≠ (block483S4 : ℝ)) :
    0 < block483V y := by
  have hcert := block483RightChunk000Certificate_eq_true
  unfold block483RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block483RightChunk000) (lo := block483RightChunk000L) (hi := block483RightChunk000R)
    (w1 := block483W1) (w2 := block483W2) (w3 := block483W3) (w4 := block483W4)
    (s1 := block483S1) (s2 := block483S2) (s3 := block483S3) (s4 := block483S4)
    hboxes hcover block483RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block483_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block483RightL : ℝ) (block483RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block483S1 : ℝ))
    (hy2ne : y ≠ (block483S2 : ℝ))
    (hy3ne : y ≠ (block483S3 : ℝ))
    (hy4ne : y ≠ (block483S4 : ℝ)) :
    0 < block483V y := by
  have hL : (block483RightChunk000L : ℝ) = (block483RightL : ℝ) := by
    norm_num [block483RightChunk000L, block483RightL]
  have hR : (block483RightChunk000R : ℝ) = (block483RightR : ℝ) := by
    norm_num [block483RightChunk000R, block483RightR]
  have hyc : y ∈ Icc (block483RightChunk000L : ℝ) (block483RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block483_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block483_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block483LeftL : ℝ) (block483LeftR : ℝ) →
    y ≠ 0 → y ≠ (block483S1 : ℝ) → y ≠ (block483S2 : ℝ) →
    y ≠ (block483S3 : ℝ) → y ≠ (block483S4 : ℝ) → 0 < block483V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block483RightL : ℝ) (block483RightR : ℝ) →
    y ≠ 0 → y ≠ (block483S1 : ℝ) → y ≠ (block483S2 : ℝ) →
    y ≠ (block483S3 : ℝ) → y ≠ (block483S4 : ℝ) → 0 < block483V y)

theorem block483_reallog_certificate_proof :
    block483_reallog_certificate := by
  exact ⟨block483_left_V_pos, block483_right_V_pos⟩

end Block483
end M1817475
end Erdos1038Lean
