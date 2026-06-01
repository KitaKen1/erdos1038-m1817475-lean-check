import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block027

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block027

open Set

def block027W1 : Rat := ((23320708309644687 : Rat) / 10000000000000000)
def block027W2 : Rat := (0 : Rat)
def block027W3 : Rat := (0 : Rat)
def block027W4 : Rat := ((28535368029314157 : Rat) / 100000000000000000)
def block027S1 : Rat := ((18174751 : Rat) / 10000000)
def block027S2 : Rat := ((511587 : Rat) / 200000)
def block027S3 : Rat := ((107000619 : Rat) / 40000000)
def block027S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block027V (y : ℝ) : ℝ :=
  ratPotential block027W1 block027W2 block027W3 block027W4 block027S1 block027S2 block027S3 block027S4 y

def block027LeftParamsCertificate : Bool :=
  allBoxesSameParams block027LeftBoxes block027W1 block027W2 block027W3 block027W4 block027S1 block027S2 block027S3 block027S4

theorem block027LeftParamsCertificate_eq_true :
    block027LeftParamsCertificate = true := by
  native_decide

theorem block027_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block027LeftL : ℝ) (block027LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block027S1 : ℝ))
    (hy2ne : y ≠ (block027S2 : ℝ))
    (hy3ne : y ≠ (block027S3 : ℝ))
    (hy4ne : y ≠ (block027S4 : ℝ)) :
    0 < block027V y := by
  have hcert := block027LeftCertificate_eq_true
  unfold block027LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block027LeftBoxes) (lo := block027LeftL) (hi := block027LeftR)
    (w1 := block027W1) (w2 := block027W2) (w3 := block027W3) (w4 := block027W4)
    (s1 := block027S1) (s2 := block027S2) (s3 := block027S3) (s4 := block027S4)
    hboxes hcover block027LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block027RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block027RightChunk000 block027W1 block027W2 block027W3 block027W4 block027S1 block027S2 block027S3 block027S4

theorem block027RightChunk000ParamsCertificate_eq_true :
    block027RightChunk000ParamsCertificate = true := by
  native_decide

theorem block027_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block027RightChunk000L : ℝ) (block027RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block027S1 : ℝ))
    (hy2ne : y ≠ (block027S2 : ℝ))
    (hy3ne : y ≠ (block027S3 : ℝ))
    (hy4ne : y ≠ (block027S4 : ℝ)) :
    0 < block027V y := by
  have hcert := block027RightChunk000Certificate_eq_true
  unfold block027RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block027RightChunk000) (lo := block027RightChunk000L) (hi := block027RightChunk000R)
    (w1 := block027W1) (w2 := block027W2) (w3 := block027W3) (w4 := block027W4)
    (s1 := block027S1) (s2 := block027S2) (s3 := block027S3) (s4 := block027S4)
    hboxes hcover block027RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block027_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block027RightL : ℝ) (block027RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block027S1 : ℝ))
    (hy2ne : y ≠ (block027S2 : ℝ))
    (hy3ne : y ≠ (block027S3 : ℝ))
    (hy4ne : y ≠ (block027S4 : ℝ)) :
    0 < block027V y := by
  have hL : (block027RightChunk000L : ℝ) = (block027RightL : ℝ) := by
    norm_num [block027RightChunk000L, block027RightL]
  have hR : (block027RightChunk000R : ℝ) = (block027RightR : ℝ) := by
    norm_num [block027RightChunk000R, block027RightR]
  have hyc : y ∈ Icc (block027RightChunk000L : ℝ) (block027RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block027_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block027_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block027LeftL : ℝ) (block027LeftR : ℝ) →
    y ≠ 0 → y ≠ (block027S1 : ℝ) → y ≠ (block027S2 : ℝ) →
    y ≠ (block027S3 : ℝ) → y ≠ (block027S4 : ℝ) → 0 < block027V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block027RightL : ℝ) (block027RightR : ℝ) →
    y ≠ 0 → y ≠ (block027S1 : ℝ) → y ≠ (block027S2 : ℝ) →
    y ≠ (block027S3 : ℝ) → y ≠ (block027S4 : ℝ) → 0 < block027V y)

theorem block027_reallog_certificate_proof :
    block027_reallog_certificate := by
  exact ⟨block027_left_V_pos, block027_right_V_pos⟩

end Block027
end M1817475
end Erdos1038Lean
