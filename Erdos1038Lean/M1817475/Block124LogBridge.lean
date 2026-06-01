import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block124

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block124

open Set

def block124W1 : Rat := ((34946579853899 : Rat) / 15625000000000)
def block124W2 : Rat := (0 : Rat)
def block124W3 : Rat := ((10450625001057069 : Rat) / 100000000000000000)
def block124W4 : Rat := ((7433601917097983 : Rat) / 50000000000000000)
def block124S1 : Rat := ((18174751 : Rat) / 10000000)
def block124S2 : Rat := ((511587 : Rat) / 200000)
def block124S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block124S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block124V (y : ℝ) : ℝ :=
  ratPotential block124W1 block124W2 block124W3 block124W4 block124S1 block124S2 block124S3 block124S4 y

def block124LeftParamsCertificate : Bool :=
  allBoxesSameParams block124LeftBoxes block124W1 block124W2 block124W3 block124W4 block124S1 block124S2 block124S3 block124S4

theorem block124LeftParamsCertificate_eq_true :
    block124LeftParamsCertificate = true := by
  native_decide

theorem block124_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block124LeftL : ℝ) (block124LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block124S1 : ℝ))
    (hy2ne : y ≠ (block124S2 : ℝ))
    (hy3ne : y ≠ (block124S3 : ℝ))
    (hy4ne : y ≠ (block124S4 : ℝ)) :
    0 < block124V y := by
  have hcert := block124LeftCertificate_eq_true
  unfold block124LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block124LeftBoxes) (lo := block124LeftL) (hi := block124LeftR)
    (w1 := block124W1) (w2 := block124W2) (w3 := block124W3) (w4 := block124W4)
    (s1 := block124S1) (s2 := block124S2) (s3 := block124S3) (s4 := block124S4)
    hboxes hcover block124LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block124RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block124RightChunk000 block124W1 block124W2 block124W3 block124W4 block124S1 block124S2 block124S3 block124S4

theorem block124RightChunk000ParamsCertificate_eq_true :
    block124RightChunk000ParamsCertificate = true := by
  native_decide

theorem block124_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block124RightChunk000L : ℝ) (block124RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block124S1 : ℝ))
    (hy2ne : y ≠ (block124S2 : ℝ))
    (hy3ne : y ≠ (block124S3 : ℝ))
    (hy4ne : y ≠ (block124S4 : ℝ)) :
    0 < block124V y := by
  have hcert := block124RightChunk000Certificate_eq_true
  unfold block124RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block124RightChunk000) (lo := block124RightChunk000L) (hi := block124RightChunk000R)
    (w1 := block124W1) (w2 := block124W2) (w3 := block124W3) (w4 := block124W4)
    (s1 := block124S1) (s2 := block124S2) (s3 := block124S3) (s4 := block124S4)
    hboxes hcover block124RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block124_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block124RightL : ℝ) (block124RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block124S1 : ℝ))
    (hy2ne : y ≠ (block124S2 : ℝ))
    (hy3ne : y ≠ (block124S3 : ℝ))
    (hy4ne : y ≠ (block124S4 : ℝ)) :
    0 < block124V y := by
  have hL : (block124RightChunk000L : ℝ) = (block124RightL : ℝ) := by
    norm_num [block124RightChunk000L, block124RightL]
  have hR : (block124RightChunk000R : ℝ) = (block124RightR : ℝ) := by
    norm_num [block124RightChunk000R, block124RightR]
  have hyc : y ∈ Icc (block124RightChunk000L : ℝ) (block124RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block124_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block124_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block124LeftL : ℝ) (block124LeftR : ℝ) →
    y ≠ 0 → y ≠ (block124S1 : ℝ) → y ≠ (block124S2 : ℝ) →
    y ≠ (block124S3 : ℝ) → y ≠ (block124S4 : ℝ) → 0 < block124V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block124RightL : ℝ) (block124RightR : ℝ) →
    y ≠ 0 → y ≠ (block124S1 : ℝ) → y ≠ (block124S2 : ℝ) →
    y ≠ (block124S3 : ℝ) → y ≠ (block124S4 : ℝ) → 0 < block124V y)

theorem block124_reallog_certificate_proof :
    block124_reallog_certificate := by
  exact ⟨block124_left_V_pos, block124_right_V_pos⟩

end Block124
end M1817475
end Erdos1038Lean
