import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block155

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block155

open Set

def block155W1 : Rat := ((10705186230334731 : Rat) / 5000000000000000)
def block155W2 : Rat := (0 : Rat)
def block155W3 : Rat := ((17228103657502333 : Rat) / 100000000000000000)
def block155W4 : Rat := ((8129899122746047 : Rat) / 100000000000000000)
def block155S1 : Rat := ((18174751 : Rat) / 10000000)
def block155S2 : Rat := ((511587 : Rat) / 200000)
def block155S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block155S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block155V (y : ℝ) : ℝ :=
  ratPotential block155W1 block155W2 block155W3 block155W4 block155S1 block155S2 block155S3 block155S4 y

def block155LeftParamsCertificate : Bool :=
  allBoxesSameParams block155LeftBoxes block155W1 block155W2 block155W3 block155W4 block155S1 block155S2 block155S3 block155S4

theorem block155LeftParamsCertificate_eq_true :
    block155LeftParamsCertificate = true := by
  native_decide

theorem block155_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block155LeftL : ℝ) (block155LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block155S1 : ℝ))
    (hy2ne : y ≠ (block155S2 : ℝ))
    (hy3ne : y ≠ (block155S3 : ℝ))
    (hy4ne : y ≠ (block155S4 : ℝ)) :
    0 < block155V y := by
  have hcert := block155LeftCertificate_eq_true
  unfold block155LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block155LeftBoxes) (lo := block155LeftL) (hi := block155LeftR)
    (w1 := block155W1) (w2 := block155W2) (w3 := block155W3) (w4 := block155W4)
    (s1 := block155S1) (s2 := block155S2) (s3 := block155S3) (s4 := block155S4)
    hboxes hcover block155LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block155RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block155RightChunk000 block155W1 block155W2 block155W3 block155W4 block155S1 block155S2 block155S3 block155S4

theorem block155RightChunk000ParamsCertificate_eq_true :
    block155RightChunk000ParamsCertificate = true := by
  native_decide

theorem block155_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block155RightChunk000L : ℝ) (block155RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block155S1 : ℝ))
    (hy2ne : y ≠ (block155S2 : ℝ))
    (hy3ne : y ≠ (block155S3 : ℝ))
    (hy4ne : y ≠ (block155S4 : ℝ)) :
    0 < block155V y := by
  have hcert := block155RightChunk000Certificate_eq_true
  unfold block155RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block155RightChunk000) (lo := block155RightChunk000L) (hi := block155RightChunk000R)
    (w1 := block155W1) (w2 := block155W2) (w3 := block155W3) (w4 := block155W4)
    (s1 := block155S1) (s2 := block155S2) (s3 := block155S3) (s4 := block155S4)
    hboxes hcover block155RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block155_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block155RightL : ℝ) (block155RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block155S1 : ℝ))
    (hy2ne : y ≠ (block155S2 : ℝ))
    (hy3ne : y ≠ (block155S3 : ℝ))
    (hy4ne : y ≠ (block155S4 : ℝ)) :
    0 < block155V y := by
  have hL : (block155RightChunk000L : ℝ) = (block155RightL : ℝ) := by
    norm_num [block155RightChunk000L, block155RightL]
  have hR : (block155RightChunk000R : ℝ) = (block155RightR : ℝ) := by
    norm_num [block155RightChunk000R, block155RightR]
  have hyc : y ∈ Icc (block155RightChunk000L : ℝ) (block155RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block155_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block155_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block155LeftL : ℝ) (block155LeftR : ℝ) →
    y ≠ 0 → y ≠ (block155S1 : ℝ) → y ≠ (block155S2 : ℝ) →
    y ≠ (block155S3 : ℝ) → y ≠ (block155S4 : ℝ) → 0 < block155V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block155RightL : ℝ) (block155RightR : ℝ) →
    y ≠ 0 → y ≠ (block155S1 : ℝ) → y ≠ (block155S2 : ℝ) →
    y ≠ (block155S3 : ℝ) → y ≠ (block155S4 : ℝ) → 0 < block155V y)

theorem block155_reallog_certificate_proof :
    block155_reallog_certificate := by
  exact ⟨block155_left_V_pos, block155_right_V_pos⟩

end Block155
end M1817475
end Erdos1038Lean
