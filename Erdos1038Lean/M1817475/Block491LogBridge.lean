import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block491

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block491

open Set

def block491W1 : Rat := ((6065725846043303 : Rat) / 12500000000000000)
def block491W2 : Rat := (0 : Rat)
def block491W3 : Rat := ((19884319980122603 : Rat) / 50000000000000000)
def block491W4 : Rat := ((1522383206970293 : Rat) / 50000000000000000)
def block491S1 : Rat := ((18174751 : Rat) / 10000000)
def block491S2 : Rat := ((511587 : Rat) / 200000)
def block491S3 : Rat := ((130534945625000000141 : Rat) / 50000000000000000000)
def block491S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block491V (y : ℝ) : ℝ :=
  ratPotential block491W1 block491W2 block491W3 block491W4 block491S1 block491S2 block491S3 block491S4 y

def block491LeftParamsCertificate : Bool :=
  allBoxesSameParams block491LeftBoxes block491W1 block491W2 block491W3 block491W4 block491S1 block491S2 block491S3 block491S4

theorem block491LeftParamsCertificate_eq_true :
    block491LeftParamsCertificate = true := by
  native_decide

theorem block491_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block491LeftL : ℝ) (block491LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block491S1 : ℝ))
    (hy2ne : y ≠ (block491S2 : ℝ))
    (hy3ne : y ≠ (block491S3 : ℝ))
    (hy4ne : y ≠ (block491S4 : ℝ)) :
    0 < block491V y := by
  have hcert := block491LeftCertificate_eq_true
  unfold block491LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block491LeftBoxes) (lo := block491LeftL) (hi := block491LeftR)
    (w1 := block491W1) (w2 := block491W2) (w3 := block491W3) (w4 := block491W4)
    (s1 := block491S1) (s2 := block491S2) (s3 := block491S3) (s4 := block491S4)
    hboxes hcover block491LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block491RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block491RightChunk000 block491W1 block491W2 block491W3 block491W4 block491S1 block491S2 block491S3 block491S4

theorem block491RightChunk000ParamsCertificate_eq_true :
    block491RightChunk000ParamsCertificate = true := by
  native_decide

theorem block491_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block491RightChunk000L : ℝ) (block491RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block491S1 : ℝ))
    (hy2ne : y ≠ (block491S2 : ℝ))
    (hy3ne : y ≠ (block491S3 : ℝ))
    (hy4ne : y ≠ (block491S4 : ℝ)) :
    0 < block491V y := by
  have hcert := block491RightChunk000Certificate_eq_true
  unfold block491RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block491RightChunk000) (lo := block491RightChunk000L) (hi := block491RightChunk000R)
    (w1 := block491W1) (w2 := block491W2) (w3 := block491W3) (w4 := block491W4)
    (s1 := block491S1) (s2 := block491S2) (s3 := block491S3) (s4 := block491S4)
    hboxes hcover block491RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block491_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block491RightL : ℝ) (block491RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block491S1 : ℝ))
    (hy2ne : y ≠ (block491S2 : ℝ))
    (hy3ne : y ≠ (block491S3 : ℝ))
    (hy4ne : y ≠ (block491S4 : ℝ)) :
    0 < block491V y := by
  have hL : (block491RightChunk000L : ℝ) = (block491RightL : ℝ) := by
    norm_num [block491RightChunk000L, block491RightL]
  have hR : (block491RightChunk000R : ℝ) = (block491RightR : ℝ) := by
    norm_num [block491RightChunk000R, block491RightR]
  have hyc : y ∈ Icc (block491RightChunk000L : ℝ) (block491RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block491_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block491_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block491LeftL : ℝ) (block491LeftR : ℝ) →
    y ≠ 0 → y ≠ (block491S1 : ℝ) → y ≠ (block491S2 : ℝ) →
    y ≠ (block491S3 : ℝ) → y ≠ (block491S4 : ℝ) → 0 < block491V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block491RightL : ℝ) (block491RightR : ℝ) →
    y ≠ 0 → y ≠ (block491S1 : ℝ) → y ≠ (block491S2 : ℝ) →
    y ≠ (block491S3 : ℝ) → y ≠ (block491S4 : ℝ) → 0 < block491V y)

theorem block491_reallog_certificate_proof :
    block491_reallog_certificate := by
  exact ⟨block491_left_V_pos, block491_right_V_pos⟩

end Block491
end M1817475
end Erdos1038Lean
