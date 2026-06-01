import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block069

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block069

open Set

def block069W1 : Rat := ((30544862836718907 : Rat) / 10000000000000000)
def block069W2 : Rat := (0 : Rat)
def block069W3 : Rat := (0 : Rat)
def block069W4 : Rat := ((12621245721450963 : Rat) / 50000000000000000)
def block069S1 : Rat := ((18174751 : Rat) / 10000000)
def block069S2 : Rat := ((511587 : Rat) / 200000)
def block069S3 : Rat := ((107000619 : Rat) / 40000000)
def block069S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block069V (y : ℝ) : ℝ :=
  ratPotential block069W1 block069W2 block069W3 block069W4 block069S1 block069S2 block069S3 block069S4 y

def block069LeftParamsCertificate : Bool :=
  allBoxesSameParams block069LeftBoxes block069W1 block069W2 block069W3 block069W4 block069S1 block069S2 block069S3 block069S4

theorem block069LeftParamsCertificate_eq_true :
    block069LeftParamsCertificate = true := by
  native_decide

theorem block069_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block069LeftL : ℝ) (block069LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block069S1 : ℝ))
    (hy2ne : y ≠ (block069S2 : ℝ))
    (hy3ne : y ≠ (block069S3 : ℝ))
    (hy4ne : y ≠ (block069S4 : ℝ)) :
    0 < block069V y := by
  have hcert := block069LeftCertificate_eq_true
  unfold block069LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block069LeftBoxes) (lo := block069LeftL) (hi := block069LeftR)
    (w1 := block069W1) (w2 := block069W2) (w3 := block069W3) (w4 := block069W4)
    (s1 := block069S1) (s2 := block069S2) (s3 := block069S3) (s4 := block069S4)
    hboxes hcover block069LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block069RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block069RightChunk000 block069W1 block069W2 block069W3 block069W4 block069S1 block069S2 block069S3 block069S4

theorem block069RightChunk000ParamsCertificate_eq_true :
    block069RightChunk000ParamsCertificate = true := by
  native_decide

theorem block069_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block069RightChunk000L : ℝ) (block069RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block069S1 : ℝ))
    (hy2ne : y ≠ (block069S2 : ℝ))
    (hy3ne : y ≠ (block069S3 : ℝ))
    (hy4ne : y ≠ (block069S4 : ℝ)) :
    0 < block069V y := by
  have hcert := block069RightChunk000Certificate_eq_true
  unfold block069RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block069RightChunk000) (lo := block069RightChunk000L) (hi := block069RightChunk000R)
    (w1 := block069W1) (w2 := block069W2) (w3 := block069W3) (w4 := block069W4)
    (s1 := block069S1) (s2 := block069S2) (s3 := block069S3) (s4 := block069S4)
    hboxes hcover block069RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block069_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block069RightL : ℝ) (block069RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block069S1 : ℝ))
    (hy2ne : y ≠ (block069S2 : ℝ))
    (hy3ne : y ≠ (block069S3 : ℝ))
    (hy4ne : y ≠ (block069S4 : ℝ)) :
    0 < block069V y := by
  have hL : (block069RightChunk000L : ℝ) = (block069RightL : ℝ) := by
    norm_num [block069RightChunk000L, block069RightL]
  have hR : (block069RightChunk000R : ℝ) = (block069RightR : ℝ) := by
    norm_num [block069RightChunk000R, block069RightR]
  have hyc : y ∈ Icc (block069RightChunk000L : ℝ) (block069RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block069_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block069_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block069LeftL : ℝ) (block069LeftR : ℝ) →
    y ≠ 0 → y ≠ (block069S1 : ℝ) → y ≠ (block069S2 : ℝ) →
    y ≠ (block069S3 : ℝ) → y ≠ (block069S4 : ℝ) → 0 < block069V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block069RightL : ℝ) (block069RightR : ℝ) →
    y ≠ 0 → y ≠ (block069S1 : ℝ) → y ≠ (block069S2 : ℝ) →
    y ≠ (block069S3 : ℝ) → y ≠ (block069S4 : ℝ) → 0 < block069V y)

theorem block069_reallog_certificate_proof :
    block069_reallog_certificate := by
  exact ⟨block069_left_V_pos, block069_right_V_pos⟩

end Block069
end M1817475
end Erdos1038Lean
