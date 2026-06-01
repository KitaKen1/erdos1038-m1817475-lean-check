import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block042

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block042

open Set

def block042W1 : Rat := ((2546567829429867 : Rat) / 1000000000000000)
def block042W2 : Rat := (0 : Rat)
def block042W3 : Rat := (0 : Rat)
def block042W4 : Rat := ((2746173519237983 : Rat) / 10000000000000000)
def block042S1 : Rat := ((18174751 : Rat) / 10000000)
def block042S2 : Rat := ((511587 : Rat) / 200000)
def block042S3 : Rat := ((107000619 : Rat) / 40000000)
def block042S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block042V (y : ℝ) : ℝ :=
  ratPotential block042W1 block042W2 block042W3 block042W4 block042S1 block042S2 block042S3 block042S4 y

def block042LeftParamsCertificate : Bool :=
  allBoxesSameParams block042LeftBoxes block042W1 block042W2 block042W3 block042W4 block042S1 block042S2 block042S3 block042S4

theorem block042LeftParamsCertificate_eq_true :
    block042LeftParamsCertificate = true := by
  native_decide

theorem block042_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block042LeftL : ℝ) (block042LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block042S1 : ℝ))
    (hy2ne : y ≠ (block042S2 : ℝ))
    (hy3ne : y ≠ (block042S3 : ℝ))
    (hy4ne : y ≠ (block042S4 : ℝ)) :
    0 < block042V y := by
  have hcert := block042LeftCertificate_eq_true
  unfold block042LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block042LeftBoxes) (lo := block042LeftL) (hi := block042LeftR)
    (w1 := block042W1) (w2 := block042W2) (w3 := block042W3) (w4 := block042W4)
    (s1 := block042S1) (s2 := block042S2) (s3 := block042S3) (s4 := block042S4)
    hboxes hcover block042LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block042RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block042RightChunk000 block042W1 block042W2 block042W3 block042W4 block042S1 block042S2 block042S3 block042S4

theorem block042RightChunk000ParamsCertificate_eq_true :
    block042RightChunk000ParamsCertificate = true := by
  native_decide

theorem block042_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block042RightChunk000L : ℝ) (block042RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block042S1 : ℝ))
    (hy2ne : y ≠ (block042S2 : ℝ))
    (hy3ne : y ≠ (block042S3 : ℝ))
    (hy4ne : y ≠ (block042S4 : ℝ)) :
    0 < block042V y := by
  have hcert := block042RightChunk000Certificate_eq_true
  unfold block042RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block042RightChunk000) (lo := block042RightChunk000L) (hi := block042RightChunk000R)
    (w1 := block042W1) (w2 := block042W2) (w3 := block042W3) (w4 := block042W4)
    (s1 := block042S1) (s2 := block042S2) (s3 := block042S3) (s4 := block042S4)
    hboxes hcover block042RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block042_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block042RightL : ℝ) (block042RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block042S1 : ℝ))
    (hy2ne : y ≠ (block042S2 : ℝ))
    (hy3ne : y ≠ (block042S3 : ℝ))
    (hy4ne : y ≠ (block042S4 : ℝ)) :
    0 < block042V y := by
  have hL : (block042RightChunk000L : ℝ) = (block042RightL : ℝ) := by
    norm_num [block042RightChunk000L, block042RightL]
  have hR : (block042RightChunk000R : ℝ) = (block042RightR : ℝ) := by
    norm_num [block042RightChunk000R, block042RightR]
  have hyc : y ∈ Icc (block042RightChunk000L : ℝ) (block042RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block042_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block042_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block042LeftL : ℝ) (block042LeftR : ℝ) →
    y ≠ 0 → y ≠ (block042S1 : ℝ) → y ≠ (block042S2 : ℝ) →
    y ≠ (block042S3 : ℝ) → y ≠ (block042S4 : ℝ) → 0 < block042V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block042RightL : ℝ) (block042RightR : ℝ) →
    y ≠ 0 → y ≠ (block042S1 : ℝ) → y ≠ (block042S2 : ℝ) →
    y ≠ (block042S3 : ℝ) → y ≠ (block042S4 : ℝ) → 0 < block042V y)

theorem block042_reallog_certificate_proof :
    block042_reallog_certificate := by
  exact ⟨block042_left_V_pos, block042_right_V_pos⟩

end Block042
end M1817475
end Erdos1038Lean
