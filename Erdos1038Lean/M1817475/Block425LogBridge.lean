import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block425

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block425

open Set

def block425W1 : Rat := ((839181314983537 : Rat) / 1250000000000000)
def block425W2 : Rat := (0 : Rat)
def block425W3 : Rat := ((15115089424969347 : Rat) / 50000000000000000)
def block425W4 : Rat := ((8241893130429791 : Rat) / 100000000000000000)
def block425S1 : Rat := ((18174751 : Rat) / 10000000)
def block425S2 : Rat := ((511587 : Rat) / 200000)
def block425S3 : Rat := ((131825186696428571513 : Rat) / 50000000000000000000)
def block425S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block425V (y : ℝ) : ℝ :=
  ratPotential block425W1 block425W2 block425W3 block425W4 block425S1 block425S2 block425S3 block425S4 y

def block425LeftParamsCertificate : Bool :=
  allBoxesSameParams block425LeftBoxes block425W1 block425W2 block425W3 block425W4 block425S1 block425S2 block425S3 block425S4

theorem block425LeftParamsCertificate_eq_true :
    block425LeftParamsCertificate = true := by
  native_decide

theorem block425_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block425LeftL : ℝ) (block425LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block425S1 : ℝ))
    (hy2ne : y ≠ (block425S2 : ℝ))
    (hy3ne : y ≠ (block425S3 : ℝ))
    (hy4ne : y ≠ (block425S4 : ℝ)) :
    0 < block425V y := by
  have hcert := block425LeftCertificate_eq_true
  unfold block425LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block425LeftBoxes) (lo := block425LeftL) (hi := block425LeftR)
    (w1 := block425W1) (w2 := block425W2) (w3 := block425W3) (w4 := block425W4)
    (s1 := block425S1) (s2 := block425S2) (s3 := block425S3) (s4 := block425S4)
    hboxes hcover block425LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block425RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block425RightChunk000 block425W1 block425W2 block425W3 block425W4 block425S1 block425S2 block425S3 block425S4

theorem block425RightChunk000ParamsCertificate_eq_true :
    block425RightChunk000ParamsCertificate = true := by
  native_decide

theorem block425_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block425RightChunk000L : ℝ) (block425RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block425S1 : ℝ))
    (hy2ne : y ≠ (block425S2 : ℝ))
    (hy3ne : y ≠ (block425S3 : ℝ))
    (hy4ne : y ≠ (block425S4 : ℝ)) :
    0 < block425V y := by
  have hcert := block425RightChunk000Certificate_eq_true
  unfold block425RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block425RightChunk000) (lo := block425RightChunk000L) (hi := block425RightChunk000R)
    (w1 := block425W1) (w2 := block425W2) (w3 := block425W3) (w4 := block425W4)
    (s1 := block425S1) (s2 := block425S2) (s3 := block425S3) (s4 := block425S4)
    hboxes hcover block425RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block425_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block425RightL : ℝ) (block425RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block425S1 : ℝ))
    (hy2ne : y ≠ (block425S2 : ℝ))
    (hy3ne : y ≠ (block425S3 : ℝ))
    (hy4ne : y ≠ (block425S4 : ℝ)) :
    0 < block425V y := by
  have hL : (block425RightChunk000L : ℝ) = (block425RightL : ℝ) := by
    norm_num [block425RightChunk000L, block425RightL]
  have hR : (block425RightChunk000R : ℝ) = (block425RightR : ℝ) := by
    norm_num [block425RightChunk000R, block425RightR]
  have hyc : y ∈ Icc (block425RightChunk000L : ℝ) (block425RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block425_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block425_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block425LeftL : ℝ) (block425LeftR : ℝ) →
    y ≠ 0 → y ≠ (block425S1 : ℝ) → y ≠ (block425S2 : ℝ) →
    y ≠ (block425S3 : ℝ) → y ≠ (block425S4 : ℝ) → 0 < block425V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block425RightL : ℝ) (block425RightR : ℝ) →
    y ≠ 0 → y ≠ (block425S1 : ℝ) → y ≠ (block425S2 : ℝ) →
    y ≠ (block425S3 : ℝ) → y ≠ (block425S4 : ℝ) → 0 < block425V y)

theorem block425_reallog_certificate_proof :
    block425_reallog_certificate := by
  exact ⟨block425_left_V_pos, block425_right_V_pos⟩

end Block425
end M1817475
end Erdos1038Lean
