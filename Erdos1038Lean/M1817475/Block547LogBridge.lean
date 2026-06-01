import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block547

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block547

open Set

def block547W1 : Rat := ((3906766130128121 : Rat) / 10000000000000000)
def block547W2 : Rat := (0 : Rat)
def block547W3 : Rat := ((2293301792789409 : Rat) / 5000000000000000)
def block547W4 : Rat := (0 : Rat)
def block547S1 : Rat := ((18174751 : Rat) / 10000000)
def block547S2 : Rat := ((511587 : Rat) / 200000)
def block547S3 : Rat := ((129440195625000000189 : Rat) / 50000000000000000000)
def block547S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block547V (y : ℝ) : ℝ :=
  ratPotential block547W1 block547W2 block547W3 block547W4 block547S1 block547S2 block547S3 block547S4 y

def block547LeftParamsCertificate : Bool :=
  allBoxesSameParams block547LeftBoxes block547W1 block547W2 block547W3 block547W4 block547S1 block547S2 block547S3 block547S4

theorem block547LeftParamsCertificate_eq_true :
    block547LeftParamsCertificate = true := by
  native_decide

theorem block547_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block547LeftL : ℝ) (block547LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block547S1 : ℝ))
    (hy2ne : y ≠ (block547S2 : ℝ))
    (hy3ne : y ≠ (block547S3 : ℝ))
    (hy4ne : y ≠ (block547S4 : ℝ)) :
    0 < block547V y := by
  have hcert := block547LeftCertificate_eq_true
  unfold block547LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block547LeftBoxes) (lo := block547LeftL) (hi := block547LeftR)
    (w1 := block547W1) (w2 := block547W2) (w3 := block547W3) (w4 := block547W4)
    (s1 := block547S1) (s2 := block547S2) (s3 := block547S3) (s4 := block547S4)
    hboxes hcover block547LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block547RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block547RightChunk000 block547W1 block547W2 block547W3 block547W4 block547S1 block547S2 block547S3 block547S4

theorem block547RightChunk000ParamsCertificate_eq_true :
    block547RightChunk000ParamsCertificate = true := by
  native_decide

theorem block547_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block547RightChunk000L : ℝ) (block547RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block547S1 : ℝ))
    (hy2ne : y ≠ (block547S2 : ℝ))
    (hy3ne : y ≠ (block547S3 : ℝ))
    (hy4ne : y ≠ (block547S4 : ℝ)) :
    0 < block547V y := by
  have hcert := block547RightChunk000Certificate_eq_true
  unfold block547RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block547RightChunk000) (lo := block547RightChunk000L) (hi := block547RightChunk000R)
    (w1 := block547W1) (w2 := block547W2) (w3 := block547W3) (w4 := block547W4)
    (s1 := block547S1) (s2 := block547S2) (s3 := block547S3) (s4 := block547S4)
    hboxes hcover block547RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block547_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block547RightL : ℝ) (block547RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block547S1 : ℝ))
    (hy2ne : y ≠ (block547S2 : ℝ))
    (hy3ne : y ≠ (block547S3 : ℝ))
    (hy4ne : y ≠ (block547S4 : ℝ)) :
    0 < block547V y := by
  have hL : (block547RightChunk000L : ℝ) = (block547RightL : ℝ) := by
    norm_num [block547RightChunk000L, block547RightL]
  have hR : (block547RightChunk000R : ℝ) = (block547RightR : ℝ) := by
    norm_num [block547RightChunk000R, block547RightR]
  have hyc : y ∈ Icc (block547RightChunk000L : ℝ) (block547RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block547_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block547_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block547LeftL : ℝ) (block547LeftR : ℝ) →
    y ≠ 0 → y ≠ (block547S1 : ℝ) → y ≠ (block547S2 : ℝ) →
    y ≠ (block547S3 : ℝ) → y ≠ (block547S4 : ℝ) → 0 < block547V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block547RightL : ℝ) (block547RightR : ℝ) →
    y ≠ 0 → y ≠ (block547S1 : ℝ) → y ≠ (block547S2 : ℝ) →
    y ≠ (block547S3 : ℝ) → y ≠ (block547S4 : ℝ) → 0 < block547V y)

theorem block547_reallog_certificate_proof :
    block547_reallog_certificate := by
  exact ⟨block547_left_V_pos, block547_right_V_pos⟩

end Block547
end M1817475
end Erdos1038Lean
