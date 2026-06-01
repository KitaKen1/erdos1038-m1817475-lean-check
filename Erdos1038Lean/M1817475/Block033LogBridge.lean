import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block033

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block033

open Set

def block033W1 : Rat := ((589199718741 : Rat) / 244140625000)
def block033W2 : Rat := (0 : Rat)
def block033W3 : Rat := (0 : Rat)
def block033W4 : Rat := ((14058598175803133 : Rat) / 50000000000000000)
def block033S1 : Rat := ((18174751 : Rat) / 10000000)
def block033S2 : Rat := ((511587 : Rat) / 200000)
def block033S3 : Rat := ((107000619 : Rat) / 40000000)
def block033S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block033V (y : ℝ) : ℝ :=
  ratPotential block033W1 block033W2 block033W3 block033W4 block033S1 block033S2 block033S3 block033S4 y

def block033LeftParamsCertificate : Bool :=
  allBoxesSameParams block033LeftBoxes block033W1 block033W2 block033W3 block033W4 block033S1 block033S2 block033S3 block033S4

theorem block033LeftParamsCertificate_eq_true :
    block033LeftParamsCertificate = true := by
  native_decide

theorem block033_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block033LeftL : ℝ) (block033LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block033S1 : ℝ))
    (hy2ne : y ≠ (block033S2 : ℝ))
    (hy3ne : y ≠ (block033S3 : ℝ))
    (hy4ne : y ≠ (block033S4 : ℝ)) :
    0 < block033V y := by
  have hcert := block033LeftCertificate_eq_true
  unfold block033LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block033LeftBoxes) (lo := block033LeftL) (hi := block033LeftR)
    (w1 := block033W1) (w2 := block033W2) (w3 := block033W3) (w4 := block033W4)
    (s1 := block033S1) (s2 := block033S2) (s3 := block033S3) (s4 := block033S4)
    hboxes hcover block033LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block033RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block033RightChunk000 block033W1 block033W2 block033W3 block033W4 block033S1 block033S2 block033S3 block033S4

theorem block033RightChunk000ParamsCertificate_eq_true :
    block033RightChunk000ParamsCertificate = true := by
  native_decide

theorem block033_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block033RightChunk000L : ℝ) (block033RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block033S1 : ℝ))
    (hy2ne : y ≠ (block033S2 : ℝ))
    (hy3ne : y ≠ (block033S3 : ℝ))
    (hy4ne : y ≠ (block033S4 : ℝ)) :
    0 < block033V y := by
  have hcert := block033RightChunk000Certificate_eq_true
  unfold block033RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block033RightChunk000) (lo := block033RightChunk000L) (hi := block033RightChunk000R)
    (w1 := block033W1) (w2 := block033W2) (w3 := block033W3) (w4 := block033W4)
    (s1 := block033S1) (s2 := block033S2) (s3 := block033S3) (s4 := block033S4)
    hboxes hcover block033RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block033_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block033RightL : ℝ) (block033RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block033S1 : ℝ))
    (hy2ne : y ≠ (block033S2 : ℝ))
    (hy3ne : y ≠ (block033S3 : ℝ))
    (hy4ne : y ≠ (block033S4 : ℝ)) :
    0 < block033V y := by
  have hL : (block033RightChunk000L : ℝ) = (block033RightL : ℝ) := by
    norm_num [block033RightChunk000L, block033RightL]
  have hR : (block033RightChunk000R : ℝ) = (block033RightR : ℝ) := by
    norm_num [block033RightChunk000R, block033RightR]
  have hyc : y ∈ Icc (block033RightChunk000L : ℝ) (block033RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block033_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block033_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block033LeftL : ℝ) (block033LeftR : ℝ) →
    y ≠ 0 → y ≠ (block033S1 : ℝ) → y ≠ (block033S2 : ℝ) →
    y ≠ (block033S3 : ℝ) → y ≠ (block033S4 : ℝ) → 0 < block033V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block033RightL : ℝ) (block033RightR : ℝ) →
    y ≠ 0 → y ≠ (block033S1 : ℝ) → y ≠ (block033S2 : ℝ) →
    y ≠ (block033S3 : ℝ) → y ≠ (block033S4 : ℝ) → 0 < block033V y)

theorem block033_reallog_certificate_proof :
    block033_reallog_certificate := by
  exact ⟨block033_left_V_pos, block033_right_V_pos⟩

end Block033
end M1817475
end Erdos1038Lean
