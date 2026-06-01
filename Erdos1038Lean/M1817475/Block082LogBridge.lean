import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block082

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block082

open Set

def block082W1 : Rat := ((8456435126348999 : Rat) / 2500000000000000)
def block082W2 : Rat := (0 : Rat)
def block082W3 : Rat := (0 : Rat)
def block082W4 : Rat := ((239944700387829 : Rat) / 1000000000000000)
def block082S1 : Rat := ((18174751 : Rat) / 10000000)
def block082S2 : Rat := ((511587 : Rat) / 200000)
def block082S3 : Rat := ((107000619 : Rat) / 40000000)
def block082S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block082V (y : ℝ) : ℝ :=
  ratPotential block082W1 block082W2 block082W3 block082W4 block082S1 block082S2 block082S3 block082S4 y

def block082LeftParamsCertificate : Bool :=
  allBoxesSameParams block082LeftBoxes block082W1 block082W2 block082W3 block082W4 block082S1 block082S2 block082S3 block082S4

theorem block082LeftParamsCertificate_eq_true :
    block082LeftParamsCertificate = true := by
  native_decide

theorem block082_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block082LeftL : ℝ) (block082LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block082S1 : ℝ))
    (hy2ne : y ≠ (block082S2 : ℝ))
    (hy3ne : y ≠ (block082S3 : ℝ))
    (hy4ne : y ≠ (block082S4 : ℝ)) :
    0 < block082V y := by
  have hcert := block082LeftCertificate_eq_true
  unfold block082LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block082LeftBoxes) (lo := block082LeftL) (hi := block082LeftR)
    (w1 := block082W1) (w2 := block082W2) (w3 := block082W3) (w4 := block082W4)
    (s1 := block082S1) (s2 := block082S2) (s3 := block082S3) (s4 := block082S4)
    hboxes hcover block082LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block082RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block082RightChunk000 block082W1 block082W2 block082W3 block082W4 block082S1 block082S2 block082S3 block082S4

theorem block082RightChunk000ParamsCertificate_eq_true :
    block082RightChunk000ParamsCertificate = true := by
  native_decide

theorem block082_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block082RightChunk000L : ℝ) (block082RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block082S1 : ℝ))
    (hy2ne : y ≠ (block082S2 : ℝ))
    (hy3ne : y ≠ (block082S3 : ℝ))
    (hy4ne : y ≠ (block082S4 : ℝ)) :
    0 < block082V y := by
  have hcert := block082RightChunk000Certificate_eq_true
  unfold block082RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block082RightChunk000) (lo := block082RightChunk000L) (hi := block082RightChunk000R)
    (w1 := block082W1) (w2 := block082W2) (w3 := block082W3) (w4 := block082W4)
    (s1 := block082S1) (s2 := block082S2) (s3 := block082S3) (s4 := block082S4)
    hboxes hcover block082RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block082_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block082RightL : ℝ) (block082RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block082S1 : ℝ))
    (hy2ne : y ≠ (block082S2 : ℝ))
    (hy3ne : y ≠ (block082S3 : ℝ))
    (hy4ne : y ≠ (block082S4 : ℝ)) :
    0 < block082V y := by
  have hL : (block082RightChunk000L : ℝ) = (block082RightL : ℝ) := by
    norm_num [block082RightChunk000L, block082RightL]
  have hR : (block082RightChunk000R : ℝ) = (block082RightR : ℝ) := by
    norm_num [block082RightChunk000R, block082RightR]
  have hyc : y ∈ Icc (block082RightChunk000L : ℝ) (block082RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block082_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block082_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block082LeftL : ℝ) (block082LeftR : ℝ) →
    y ≠ 0 → y ≠ (block082S1 : ℝ) → y ≠ (block082S2 : ℝ) →
    y ≠ (block082S3 : ℝ) → y ≠ (block082S4 : ℝ) → 0 < block082V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block082RightL : ℝ) (block082RightR : ℝ) →
    y ≠ 0 → y ≠ (block082S1 : ℝ) → y ≠ (block082S2 : ℝ) →
    y ≠ (block082S3 : ℝ) → y ≠ (block082S4 : ℝ) → 0 < block082V y)

theorem block082_reallog_certificate_proof :
    block082_reallog_certificate := by
  exact ⟨block082_left_V_pos, block082_right_V_pos⟩

end Block082
end M1817475
end Erdos1038Lean
