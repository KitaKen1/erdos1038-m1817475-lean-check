import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block029

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block029

open Set

def block029W1 : Rat := ((943420885535261 : Rat) / 400000000000000)
def block029W2 : Rat := (0 : Rat)
def block029W3 : Rat := (0 : Rat)
def block029W4 : Rat := ((5679509817629097 : Rat) / 20000000000000000)
def block029S1 : Rat := ((18174751 : Rat) / 10000000)
def block029S2 : Rat := ((511587 : Rat) / 200000)
def block029S3 : Rat := ((107000619 : Rat) / 40000000)
def block029S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block029V (y : ℝ) : ℝ :=
  ratPotential block029W1 block029W2 block029W3 block029W4 block029S1 block029S2 block029S3 block029S4 y

def block029LeftParamsCertificate : Bool :=
  allBoxesSameParams block029LeftBoxes block029W1 block029W2 block029W3 block029W4 block029S1 block029S2 block029S3 block029S4

theorem block029LeftParamsCertificate_eq_true :
    block029LeftParamsCertificate = true := by
  native_decide

theorem block029_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block029LeftL : ℝ) (block029LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block029S1 : ℝ))
    (hy2ne : y ≠ (block029S2 : ℝ))
    (hy3ne : y ≠ (block029S3 : ℝ))
    (hy4ne : y ≠ (block029S4 : ℝ)) :
    0 < block029V y := by
  have hcert := block029LeftCertificate_eq_true
  unfold block029LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block029LeftBoxes) (lo := block029LeftL) (hi := block029LeftR)
    (w1 := block029W1) (w2 := block029W2) (w3 := block029W3) (w4 := block029W4)
    (s1 := block029S1) (s2 := block029S2) (s3 := block029S3) (s4 := block029S4)
    hboxes hcover block029LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block029RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block029RightChunk000 block029W1 block029W2 block029W3 block029W4 block029S1 block029S2 block029S3 block029S4

theorem block029RightChunk000ParamsCertificate_eq_true :
    block029RightChunk000ParamsCertificate = true := by
  native_decide

theorem block029_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block029RightChunk000L : ℝ) (block029RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block029S1 : ℝ))
    (hy2ne : y ≠ (block029S2 : ℝ))
    (hy3ne : y ≠ (block029S3 : ℝ))
    (hy4ne : y ≠ (block029S4 : ℝ)) :
    0 < block029V y := by
  have hcert := block029RightChunk000Certificate_eq_true
  unfold block029RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block029RightChunk000) (lo := block029RightChunk000L) (hi := block029RightChunk000R)
    (w1 := block029W1) (w2 := block029W2) (w3 := block029W3) (w4 := block029W4)
    (s1 := block029S1) (s2 := block029S2) (s3 := block029S3) (s4 := block029S4)
    hboxes hcover block029RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block029_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block029RightL : ℝ) (block029RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block029S1 : ℝ))
    (hy2ne : y ≠ (block029S2 : ℝ))
    (hy3ne : y ≠ (block029S3 : ℝ))
    (hy4ne : y ≠ (block029S4 : ℝ)) :
    0 < block029V y := by
  have hL : (block029RightChunk000L : ℝ) = (block029RightL : ℝ) := by
    norm_num [block029RightChunk000L, block029RightL]
  have hR : (block029RightChunk000R : ℝ) = (block029RightR : ℝ) := by
    norm_num [block029RightChunk000R, block029RightR]
  have hyc : y ∈ Icc (block029RightChunk000L : ℝ) (block029RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block029_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block029_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block029LeftL : ℝ) (block029LeftR : ℝ) →
    y ≠ 0 → y ≠ (block029S1 : ℝ) → y ≠ (block029S2 : ℝ) →
    y ≠ (block029S3 : ℝ) → y ≠ (block029S4 : ℝ) → 0 < block029V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block029RightL : ℝ) (block029RightR : ℝ) →
    y ≠ 0 → y ≠ (block029S1 : ℝ) → y ≠ (block029S2 : ℝ) →
    y ≠ (block029S3 : ℝ) → y ≠ (block029S4 : ℝ) → 0 < block029V y)

theorem block029_reallog_certificate_proof :
    block029_reallog_certificate := by
  exact ⟨block029_left_V_pos, block029_right_V_pos⟩

end Block029
end M1817475
end Erdos1038Lean
