import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block079

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block079

open Set

def block079W1 : Rat := ((3300461395997301 : Rat) / 1000000000000000)
def block079W2 : Rat := (0 : Rat)
def block079W3 : Rat := (0 : Rat)
def block079W4 : Rat := ((242954394670203 : Rat) / 1000000000000000)
def block079S1 : Rat := ((18174751 : Rat) / 10000000)
def block079S2 : Rat := ((511587 : Rat) / 200000)
def block079S3 : Rat := ((107000619 : Rat) / 40000000)
def block079S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block079V (y : ℝ) : ℝ :=
  ratPotential block079W1 block079W2 block079W3 block079W4 block079S1 block079S2 block079S3 block079S4 y

def block079LeftParamsCertificate : Bool :=
  allBoxesSameParams block079LeftBoxes block079W1 block079W2 block079W3 block079W4 block079S1 block079S2 block079S3 block079S4

theorem block079LeftParamsCertificate_eq_true :
    block079LeftParamsCertificate = true := by
  native_decide

theorem block079_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block079LeftL : ℝ) (block079LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block079S1 : ℝ))
    (hy2ne : y ≠ (block079S2 : ℝ))
    (hy3ne : y ≠ (block079S3 : ℝ))
    (hy4ne : y ≠ (block079S4 : ℝ)) :
    0 < block079V y := by
  have hcert := block079LeftCertificate_eq_true
  unfold block079LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block079LeftBoxes) (lo := block079LeftL) (hi := block079LeftR)
    (w1 := block079W1) (w2 := block079W2) (w3 := block079W3) (w4 := block079W4)
    (s1 := block079S1) (s2 := block079S2) (s3 := block079S3) (s4 := block079S4)
    hboxes hcover block079LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block079RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block079RightChunk000 block079W1 block079W2 block079W3 block079W4 block079S1 block079S2 block079S3 block079S4

theorem block079RightChunk000ParamsCertificate_eq_true :
    block079RightChunk000ParamsCertificate = true := by
  native_decide

theorem block079_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block079RightChunk000L : ℝ) (block079RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block079S1 : ℝ))
    (hy2ne : y ≠ (block079S2 : ℝ))
    (hy3ne : y ≠ (block079S3 : ℝ))
    (hy4ne : y ≠ (block079S4 : ℝ)) :
    0 < block079V y := by
  have hcert := block079RightChunk000Certificate_eq_true
  unfold block079RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block079RightChunk000) (lo := block079RightChunk000L) (hi := block079RightChunk000R)
    (w1 := block079W1) (w2 := block079W2) (w3 := block079W3) (w4 := block079W4)
    (s1 := block079S1) (s2 := block079S2) (s3 := block079S3) (s4 := block079S4)
    hboxes hcover block079RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block079_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block079RightL : ℝ) (block079RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block079S1 : ℝ))
    (hy2ne : y ≠ (block079S2 : ℝ))
    (hy3ne : y ≠ (block079S3 : ℝ))
    (hy4ne : y ≠ (block079S4 : ℝ)) :
    0 < block079V y := by
  have hL : (block079RightChunk000L : ℝ) = (block079RightL : ℝ) := by
    norm_num [block079RightChunk000L, block079RightL]
  have hR : (block079RightChunk000R : ℝ) = (block079RightR : ℝ) := by
    norm_num [block079RightChunk000R, block079RightR]
  have hyc : y ∈ Icc (block079RightChunk000L : ℝ) (block079RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block079_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block079_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block079LeftL : ℝ) (block079LeftR : ℝ) →
    y ≠ 0 → y ≠ (block079S1 : ℝ) → y ≠ (block079S2 : ℝ) →
    y ≠ (block079S3 : ℝ) → y ≠ (block079S4 : ℝ) → 0 < block079V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block079RightL : ℝ) (block079RightR : ℝ) →
    y ≠ 0 → y ≠ (block079S1 : ℝ) → y ≠ (block079S2 : ℝ) →
    y ≠ (block079S3 : ℝ) → y ≠ (block079S4 : ℝ) → 0 < block079V y)

theorem block079_reallog_certificate_proof :
    block079_reallog_certificate := by
  exact ⟨block079_left_V_pos, block079_right_V_pos⟩

end Block079
end M1817475
end Erdos1038Lean
