import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block469

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block469

open Set

def block469W1 : Rat := ((1361258456111193 : Rat) / 2500000000000000)
def block469W2 : Rat := (0 : Rat)
def block469W3 : Rat := ((36020756032077883 : Rat) / 100000000000000000)
def block469W4 : Rat := ((5239718394445133 : Rat) / 100000000000000000)
def block469S1 : Rat := ((18174751 : Rat) / 10000000)
def block469S2 : Rat := ((511587 : Rat) / 200000)
def block469S3 : Rat := ((26193005196428571453 : Rat) / 10000000000000000000)
def block469S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block469V (y : ℝ) : ℝ :=
  ratPotential block469W1 block469W2 block469W3 block469W4 block469S1 block469S2 block469S3 block469S4 y

def block469LeftParamsCertificate : Bool :=
  allBoxesSameParams block469LeftBoxes block469W1 block469W2 block469W3 block469W4 block469S1 block469S2 block469S3 block469S4

theorem block469LeftParamsCertificate_eq_true :
    block469LeftParamsCertificate = true := by
  native_decide

theorem block469_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block469LeftL : ℝ) (block469LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block469S1 : ℝ))
    (hy2ne : y ≠ (block469S2 : ℝ))
    (hy3ne : y ≠ (block469S3 : ℝ))
    (hy4ne : y ≠ (block469S4 : ℝ)) :
    0 < block469V y := by
  have hcert := block469LeftCertificate_eq_true
  unfold block469LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block469LeftBoxes) (lo := block469LeftL) (hi := block469LeftR)
    (w1 := block469W1) (w2 := block469W2) (w3 := block469W3) (w4 := block469W4)
    (s1 := block469S1) (s2 := block469S2) (s3 := block469S3) (s4 := block469S4)
    hboxes hcover block469LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block469RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block469RightChunk000 block469W1 block469W2 block469W3 block469W4 block469S1 block469S2 block469S3 block469S4

theorem block469RightChunk000ParamsCertificate_eq_true :
    block469RightChunk000ParamsCertificate = true := by
  native_decide

theorem block469_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block469RightChunk000L : ℝ) (block469RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block469S1 : ℝ))
    (hy2ne : y ≠ (block469S2 : ℝ))
    (hy3ne : y ≠ (block469S3 : ℝ))
    (hy4ne : y ≠ (block469S4 : ℝ)) :
    0 < block469V y := by
  have hcert := block469RightChunk000Certificate_eq_true
  unfold block469RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block469RightChunk000) (lo := block469RightChunk000L) (hi := block469RightChunk000R)
    (w1 := block469W1) (w2 := block469W2) (w3 := block469W3) (w4 := block469W4)
    (s1 := block469S1) (s2 := block469S2) (s3 := block469S3) (s4 := block469S4)
    hboxes hcover block469RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block469_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block469RightL : ℝ) (block469RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block469S1 : ℝ))
    (hy2ne : y ≠ (block469S2 : ℝ))
    (hy3ne : y ≠ (block469S3 : ℝ))
    (hy4ne : y ≠ (block469S4 : ℝ)) :
    0 < block469V y := by
  have hL : (block469RightChunk000L : ℝ) = (block469RightL : ℝ) := by
    norm_num [block469RightChunk000L, block469RightL]
  have hR : (block469RightChunk000R : ℝ) = (block469RightR : ℝ) := by
    norm_num [block469RightChunk000R, block469RightR]
  have hyc : y ∈ Icc (block469RightChunk000L : ℝ) (block469RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block469_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block469_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block469LeftL : ℝ) (block469LeftR : ℝ) →
    y ≠ 0 → y ≠ (block469S1 : ℝ) → y ≠ (block469S2 : ℝ) →
    y ≠ (block469S3 : ℝ) → y ≠ (block469S4 : ℝ) → 0 < block469V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block469RightL : ℝ) (block469RightR : ℝ) →
    y ≠ 0 → y ≠ (block469S1 : ℝ) → y ≠ (block469S2 : ℝ) →
    y ≠ (block469S3 : ℝ) → y ≠ (block469S4 : ℝ) → 0 < block469V y)

theorem block469_reallog_certificate_proof :
    block469_reallog_certificate := by
  exact ⟨block469_left_V_pos, block469_right_V_pos⟩

end Block469
end M1817475
end Erdos1038Lean
