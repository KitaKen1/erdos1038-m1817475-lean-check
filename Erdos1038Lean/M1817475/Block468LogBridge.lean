import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block468

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block468

open Set

def block468W1 : Rat := ((1094318493931637 : Rat) / 2000000000000000)
def block468W2 : Rat := (0 : Rat)
def block468W3 : Rat := ((3587462372751749 : Rat) / 10000000000000000)
def block468W4 : Rat := ((5320311937837771 : Rat) / 100000000000000000)
def block468S1 : Rat := ((18174751 : Rat) / 10000000)
def block468S2 : Rat := ((511587 : Rat) / 200000)
def block468S3 : Rat := ((130984575089285714407 : Rat) / 50000000000000000000)
def block468S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block468V (y : ℝ) : ℝ :=
  ratPotential block468W1 block468W2 block468W3 block468W4 block468S1 block468S2 block468S3 block468S4 y

def block468LeftParamsCertificate : Bool :=
  allBoxesSameParams block468LeftBoxes block468W1 block468W2 block468W3 block468W4 block468S1 block468S2 block468S3 block468S4

theorem block468LeftParamsCertificate_eq_true :
    block468LeftParamsCertificate = true := by
  native_decide

theorem block468_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block468LeftL : ℝ) (block468LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block468S1 : ℝ))
    (hy2ne : y ≠ (block468S2 : ℝ))
    (hy3ne : y ≠ (block468S3 : ℝ))
    (hy4ne : y ≠ (block468S4 : ℝ)) :
    0 < block468V y := by
  have hcert := block468LeftCertificate_eq_true
  unfold block468LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block468LeftBoxes) (lo := block468LeftL) (hi := block468LeftR)
    (w1 := block468W1) (w2 := block468W2) (w3 := block468W3) (w4 := block468W4)
    (s1 := block468S1) (s2 := block468S2) (s3 := block468S3) (s4 := block468S4)
    hboxes hcover block468LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block468RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block468RightChunk000 block468W1 block468W2 block468W3 block468W4 block468S1 block468S2 block468S3 block468S4

theorem block468RightChunk000ParamsCertificate_eq_true :
    block468RightChunk000ParamsCertificate = true := by
  native_decide

theorem block468_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block468RightChunk000L : ℝ) (block468RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block468S1 : ℝ))
    (hy2ne : y ≠ (block468S2 : ℝ))
    (hy3ne : y ≠ (block468S3 : ℝ))
    (hy4ne : y ≠ (block468S4 : ℝ)) :
    0 < block468V y := by
  have hcert := block468RightChunk000Certificate_eq_true
  unfold block468RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block468RightChunk000) (lo := block468RightChunk000L) (hi := block468RightChunk000R)
    (w1 := block468W1) (w2 := block468W2) (w3 := block468W3) (w4 := block468W4)
    (s1 := block468S1) (s2 := block468S2) (s3 := block468S3) (s4 := block468S4)
    hboxes hcover block468RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block468_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block468RightL : ℝ) (block468RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block468S1 : ℝ))
    (hy2ne : y ≠ (block468S2 : ℝ))
    (hy3ne : y ≠ (block468S3 : ℝ))
    (hy4ne : y ≠ (block468S4 : ℝ)) :
    0 < block468V y := by
  have hL : (block468RightChunk000L : ℝ) = (block468RightL : ℝ) := by
    norm_num [block468RightChunk000L, block468RightL]
  have hR : (block468RightChunk000R : ℝ) = (block468RightR : ℝ) := by
    norm_num [block468RightChunk000R, block468RightR]
  have hyc : y ∈ Icc (block468RightChunk000L : ℝ) (block468RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block468_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block468_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block468LeftL : ℝ) (block468LeftR : ℝ) →
    y ≠ 0 → y ≠ (block468S1 : ℝ) → y ≠ (block468S2 : ℝ) →
    y ≠ (block468S3 : ℝ) → y ≠ (block468S4 : ℝ) → 0 < block468V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block468RightL : ℝ) (block468RightR : ℝ) →
    y ≠ 0 → y ≠ (block468S1 : ℝ) → y ≠ (block468S2 : ℝ) →
    y ≠ (block468S3 : ℝ) → y ≠ (block468S4 : ℝ) → 0 < block468V y)

theorem block468_reallog_certificate_proof :
    block468_reallog_certificate := by
  exact ⟨block468_left_V_pos, block468_right_V_pos⟩

end Block468
end M1817475
end Erdos1038Lean
