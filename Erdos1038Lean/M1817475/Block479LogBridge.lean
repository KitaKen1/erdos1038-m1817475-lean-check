import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block479

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block479

open Set

def block479W1 : Rat := ((5170463713803767 : Rat) / 10000000000000000)
def block479W2 : Rat := (0 : Rat)
def block479W3 : Rat := ((9416009413535599 : Rat) / 25000000000000000)
def block479W4 : Rat := ((4292382438024327 : Rat) / 100000000000000000)
def block479S1 : Rat := ((18174751 : Rat) / 10000000)
def block479S2 : Rat := ((511587 : Rat) / 200000)
def block479S3 : Rat := ((26153906982142857169 : Rat) / 10000000000000000000)
def block479S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block479V (y : ℝ) : ℝ :=
  ratPotential block479W1 block479W2 block479W3 block479W4 block479S1 block479S2 block479S3 block479S4 y

def block479LeftParamsCertificate : Bool :=
  allBoxesSameParams block479LeftBoxes block479W1 block479W2 block479W3 block479W4 block479S1 block479S2 block479S3 block479S4

theorem block479LeftParamsCertificate_eq_true :
    block479LeftParamsCertificate = true := by
  native_decide

theorem block479_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block479LeftL : ℝ) (block479LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block479S1 : ℝ))
    (hy2ne : y ≠ (block479S2 : ℝ))
    (hy3ne : y ≠ (block479S3 : ℝ))
    (hy4ne : y ≠ (block479S4 : ℝ)) :
    0 < block479V y := by
  have hcert := block479LeftCertificate_eq_true
  unfold block479LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block479LeftBoxes) (lo := block479LeftL) (hi := block479LeftR)
    (w1 := block479W1) (w2 := block479W2) (w3 := block479W3) (w4 := block479W4)
    (s1 := block479S1) (s2 := block479S2) (s3 := block479S3) (s4 := block479S4)
    hboxes hcover block479LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block479RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block479RightChunk000 block479W1 block479W2 block479W3 block479W4 block479S1 block479S2 block479S3 block479S4

theorem block479RightChunk000ParamsCertificate_eq_true :
    block479RightChunk000ParamsCertificate = true := by
  native_decide

theorem block479_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block479RightChunk000L : ℝ) (block479RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block479S1 : ℝ))
    (hy2ne : y ≠ (block479S2 : ℝ))
    (hy3ne : y ≠ (block479S3 : ℝ))
    (hy4ne : y ≠ (block479S4 : ℝ)) :
    0 < block479V y := by
  have hcert := block479RightChunk000Certificate_eq_true
  unfold block479RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block479RightChunk000) (lo := block479RightChunk000L) (hi := block479RightChunk000R)
    (w1 := block479W1) (w2 := block479W2) (w3 := block479W3) (w4 := block479W4)
    (s1 := block479S1) (s2 := block479S2) (s3 := block479S3) (s4 := block479S4)
    hboxes hcover block479RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block479_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block479RightL : ℝ) (block479RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block479S1 : ℝ))
    (hy2ne : y ≠ (block479S2 : ℝ))
    (hy3ne : y ≠ (block479S3 : ℝ))
    (hy4ne : y ≠ (block479S4 : ℝ)) :
    0 < block479V y := by
  have hL : (block479RightChunk000L : ℝ) = (block479RightL : ℝ) := by
    norm_num [block479RightChunk000L, block479RightL]
  have hR : (block479RightChunk000R : ℝ) = (block479RightR : ℝ) := by
    norm_num [block479RightChunk000R, block479RightR]
  have hyc : y ∈ Icc (block479RightChunk000L : ℝ) (block479RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block479_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block479_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block479LeftL : ℝ) (block479LeftR : ℝ) →
    y ≠ 0 → y ≠ (block479S1 : ℝ) → y ≠ (block479S2 : ℝ) →
    y ≠ (block479S3 : ℝ) → y ≠ (block479S4 : ℝ) → 0 < block479V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block479RightL : ℝ) (block479RightR : ℝ) →
    y ≠ 0 → y ≠ (block479S1 : ℝ) → y ≠ (block479S2 : ℝ) →
    y ≠ (block479S3 : ℝ) → y ≠ (block479S4 : ℝ) → 0 < block479V y)

theorem block479_reallog_certificate_proof :
    block479_reallog_certificate := by
  exact ⟨block479_left_V_pos, block479_right_V_pos⟩

end Block479
end M1817475
end Erdos1038Lean
