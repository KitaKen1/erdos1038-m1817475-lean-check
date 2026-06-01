import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block527

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block527

open Set

def block527W1 : Rat := ((20547092876674797 : Rat) / 50000000000000000)
def block527W2 : Rat := (0 : Rat)
def block527W3 : Rat := ((4510551217335963 : Rat) / 10000000000000000)
def block527W4 : Rat := (0 : Rat)
def block527S1 : Rat := ((18174751 : Rat) / 10000000)
def block527S2 : Rat := ((511587 : Rat) / 200000)
def block527S3 : Rat := ((129831177767857143029 : Rat) / 50000000000000000000)
def block527S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block527V (y : ℝ) : ℝ :=
  ratPotential block527W1 block527W2 block527W3 block527W4 block527S1 block527S2 block527S3 block527S4 y

def block527LeftParamsCertificate : Bool :=
  allBoxesSameParams block527LeftBoxes block527W1 block527W2 block527W3 block527W4 block527S1 block527S2 block527S3 block527S4

theorem block527LeftParamsCertificate_eq_true :
    block527LeftParamsCertificate = true := by
  native_decide

theorem block527_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block527LeftL : ℝ) (block527LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block527S1 : ℝ))
    (hy2ne : y ≠ (block527S2 : ℝ))
    (hy3ne : y ≠ (block527S3 : ℝ))
    (hy4ne : y ≠ (block527S4 : ℝ)) :
    0 < block527V y := by
  have hcert := block527LeftCertificate_eq_true
  unfold block527LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block527LeftBoxes) (lo := block527LeftL) (hi := block527LeftR)
    (w1 := block527W1) (w2 := block527W2) (w3 := block527W3) (w4 := block527W4)
    (s1 := block527S1) (s2 := block527S2) (s3 := block527S3) (s4 := block527S4)
    hboxes hcover block527LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block527RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block527RightChunk000 block527W1 block527W2 block527W3 block527W4 block527S1 block527S2 block527S3 block527S4

theorem block527RightChunk000ParamsCertificate_eq_true :
    block527RightChunk000ParamsCertificate = true := by
  native_decide

theorem block527_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block527RightChunk000L : ℝ) (block527RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block527S1 : ℝ))
    (hy2ne : y ≠ (block527S2 : ℝ))
    (hy3ne : y ≠ (block527S3 : ℝ))
    (hy4ne : y ≠ (block527S4 : ℝ)) :
    0 < block527V y := by
  have hcert := block527RightChunk000Certificate_eq_true
  unfold block527RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block527RightChunk000) (lo := block527RightChunk000L) (hi := block527RightChunk000R)
    (w1 := block527W1) (w2 := block527W2) (w3 := block527W3) (w4 := block527W4)
    (s1 := block527S1) (s2 := block527S2) (s3 := block527S3) (s4 := block527S4)
    hboxes hcover block527RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block527_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block527RightL : ℝ) (block527RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block527S1 : ℝ))
    (hy2ne : y ≠ (block527S2 : ℝ))
    (hy3ne : y ≠ (block527S3 : ℝ))
    (hy4ne : y ≠ (block527S4 : ℝ)) :
    0 < block527V y := by
  have hL : (block527RightChunk000L : ℝ) = (block527RightL : ℝ) := by
    norm_num [block527RightChunk000L, block527RightL]
  have hR : (block527RightChunk000R : ℝ) = (block527RightR : ℝ) := by
    norm_num [block527RightChunk000R, block527RightR]
  have hyc : y ∈ Icc (block527RightChunk000L : ℝ) (block527RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block527_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block527_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block527LeftL : ℝ) (block527LeftR : ℝ) →
    y ≠ 0 → y ≠ (block527S1 : ℝ) → y ≠ (block527S2 : ℝ) →
    y ≠ (block527S3 : ℝ) → y ≠ (block527S4 : ℝ) → 0 < block527V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block527RightL : ℝ) (block527RightR : ℝ) →
    y ≠ 0 → y ≠ (block527S1 : ℝ) → y ≠ (block527S2 : ℝ) →
    y ≠ (block527S3 : ℝ) → y ≠ (block527S4 : ℝ) → 0 < block527V y)

theorem block527_reallog_certificate_proof :
    block527_reallog_certificate := by
  exact ⟨block527_left_V_pos, block527_right_V_pos⟩

end Block527
end M1817475
end Erdos1038Lean
