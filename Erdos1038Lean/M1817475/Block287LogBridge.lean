import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block287

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block287

open Set

def block287W1 : Rat := ((2058087492174479 : Rat) / 2000000000000000)
def block287W2 : Rat := ((1134904815818323 : Rat) / 31250000000000000)
def block287W3 : Rat := ((28177492560382167 : Rat) / 100000000000000000)
def block287W4 : Rat := (0 : Rat)
def block287S1 : Rat := ((18174751 : Rat) / 10000000)
def block287S2 : Rat := ((511587 : Rat) / 200000)
def block287S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block287S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block287V (y : ℝ) : ℝ :=
  ratPotential block287W1 block287W2 block287W3 block287W4 block287S1 block287S2 block287S3 block287S4 y

def block287LeftParamsCertificate : Bool :=
  allBoxesSameParams block287LeftBoxes block287W1 block287W2 block287W3 block287W4 block287S1 block287S2 block287S3 block287S4

theorem block287LeftParamsCertificate_eq_true :
    block287LeftParamsCertificate = true := by
  native_decide

theorem block287_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block287LeftL : ℝ) (block287LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block287S1 : ℝ))
    (hy2ne : y ≠ (block287S2 : ℝ))
    (hy3ne : y ≠ (block287S3 : ℝ))
    (hy4ne : y ≠ (block287S4 : ℝ)) :
    0 < block287V y := by
  have hcert := block287LeftCertificate_eq_true
  unfold block287LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block287LeftBoxes) (lo := block287LeftL) (hi := block287LeftR)
    (w1 := block287W1) (w2 := block287W2) (w3 := block287W3) (w4 := block287W4)
    (s1 := block287S1) (s2 := block287S2) (s3 := block287S3) (s4 := block287S4)
    hboxes hcover block287LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block287RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block287RightChunk000 block287W1 block287W2 block287W3 block287W4 block287S1 block287S2 block287S3 block287S4

theorem block287RightChunk000ParamsCertificate_eq_true :
    block287RightChunk000ParamsCertificate = true := by
  native_decide

theorem block287_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block287RightChunk000L : ℝ) (block287RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block287S1 : ℝ))
    (hy2ne : y ≠ (block287S2 : ℝ))
    (hy3ne : y ≠ (block287S3 : ℝ))
    (hy4ne : y ≠ (block287S4 : ℝ)) :
    0 < block287V y := by
  have hcert := block287RightChunk000Certificate_eq_true
  unfold block287RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block287RightChunk000) (lo := block287RightChunk000L) (hi := block287RightChunk000R)
    (w1 := block287W1) (w2 := block287W2) (w3 := block287W3) (w4 := block287W4)
    (s1 := block287S1) (s2 := block287S2) (s3 := block287S3) (s4 := block287S4)
    hboxes hcover block287RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block287_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block287RightL : ℝ) (block287RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block287S1 : ℝ))
    (hy2ne : y ≠ (block287S2 : ℝ))
    (hy3ne : y ≠ (block287S3 : ℝ))
    (hy4ne : y ≠ (block287S4 : ℝ)) :
    0 < block287V y := by
  have hL : (block287RightChunk000L : ℝ) = (block287RightL : ℝ) := by
    norm_num [block287RightChunk000L, block287RightL]
  have hR : (block287RightChunk000R : ℝ) = (block287RightR : ℝ) := by
    norm_num [block287RightChunk000R, block287RightR]
  have hyc : y ∈ Icc (block287RightChunk000L : ℝ) (block287RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block287_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block287_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block287LeftL : ℝ) (block287LeftR : ℝ) →
    y ≠ 0 → y ≠ (block287S1 : ℝ) → y ≠ (block287S2 : ℝ) →
    y ≠ (block287S3 : ℝ) → y ≠ (block287S4 : ℝ) → 0 < block287V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block287RightL : ℝ) (block287RightR : ℝ) →
    y ≠ 0 → y ≠ (block287S1 : ℝ) → y ≠ (block287S2 : ℝ) →
    y ≠ (block287S3 : ℝ) → y ≠ (block287S4 : ℝ) → 0 < block287V y)

theorem block287_reallog_certificate_proof :
    block287_reallog_certificate := by
  exact ⟨block287_left_V_pos, block287_right_V_pos⟩

end Block287
end M1817475
end Erdos1038Lean
