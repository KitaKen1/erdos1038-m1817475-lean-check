import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block054

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block054

open Set

def block054W1 : Rat := ((5498481526940247 : Rat) / 2000000000000000)
def block054W2 : Rat := (0 : Rat)
def block054W3 : Rat := (0 : Rat)
def block054W4 : Rat := ((2652761768002329 : Rat) / 10000000000000000)
def block054S1 : Rat := ((18174751 : Rat) / 10000000)
def block054S2 : Rat := ((511587 : Rat) / 200000)
def block054S3 : Rat := ((107000619 : Rat) / 40000000)
def block054S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block054V (y : ℝ) : ℝ :=
  ratPotential block054W1 block054W2 block054W3 block054W4 block054S1 block054S2 block054S3 block054S4 y

def block054LeftParamsCertificate : Bool :=
  allBoxesSameParams block054LeftBoxes block054W1 block054W2 block054W3 block054W4 block054S1 block054S2 block054S3 block054S4

theorem block054LeftParamsCertificate_eq_true :
    block054LeftParamsCertificate = true := by
  native_decide

theorem block054_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block054LeftL : ℝ) (block054LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block054S1 : ℝ))
    (hy2ne : y ≠ (block054S2 : ℝ))
    (hy3ne : y ≠ (block054S3 : ℝ))
    (hy4ne : y ≠ (block054S4 : ℝ)) :
    0 < block054V y := by
  have hcert := block054LeftCertificate_eq_true
  unfold block054LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block054LeftBoxes) (lo := block054LeftL) (hi := block054LeftR)
    (w1 := block054W1) (w2 := block054W2) (w3 := block054W3) (w4 := block054W4)
    (s1 := block054S1) (s2 := block054S2) (s3 := block054S3) (s4 := block054S4)
    hboxes hcover block054LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block054RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block054RightChunk000 block054W1 block054W2 block054W3 block054W4 block054S1 block054S2 block054S3 block054S4

theorem block054RightChunk000ParamsCertificate_eq_true :
    block054RightChunk000ParamsCertificate = true := by
  native_decide

theorem block054_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block054RightChunk000L : ℝ) (block054RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block054S1 : ℝ))
    (hy2ne : y ≠ (block054S2 : ℝ))
    (hy3ne : y ≠ (block054S3 : ℝ))
    (hy4ne : y ≠ (block054S4 : ℝ)) :
    0 < block054V y := by
  have hcert := block054RightChunk000Certificate_eq_true
  unfold block054RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block054RightChunk000) (lo := block054RightChunk000L) (hi := block054RightChunk000R)
    (w1 := block054W1) (w2 := block054W2) (w3 := block054W3) (w4 := block054W4)
    (s1 := block054S1) (s2 := block054S2) (s3 := block054S3) (s4 := block054S4)
    hboxes hcover block054RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block054_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block054RightL : ℝ) (block054RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block054S1 : ℝ))
    (hy2ne : y ≠ (block054S2 : ℝ))
    (hy3ne : y ≠ (block054S3 : ℝ))
    (hy4ne : y ≠ (block054S4 : ℝ)) :
    0 < block054V y := by
  have hL : (block054RightChunk000L : ℝ) = (block054RightL : ℝ) := by
    norm_num [block054RightChunk000L, block054RightL]
  have hR : (block054RightChunk000R : ℝ) = (block054RightR : ℝ) := by
    norm_num [block054RightChunk000R, block054RightR]
  have hyc : y ∈ Icc (block054RightChunk000L : ℝ) (block054RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block054_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block054_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block054LeftL : ℝ) (block054LeftR : ℝ) →
    y ≠ 0 → y ≠ (block054S1 : ℝ) → y ≠ (block054S2 : ℝ) →
    y ≠ (block054S3 : ℝ) → y ≠ (block054S4 : ℝ) → 0 < block054V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block054RightL : ℝ) (block054RightR : ℝ) →
    y ≠ 0 → y ≠ (block054S1 : ℝ) → y ≠ (block054S2 : ℝ) →
    y ≠ (block054S3 : ℝ) → y ≠ (block054S4 : ℝ) → 0 < block054V y)

theorem block054_reallog_certificate_proof :
    block054_reallog_certificate := by
  exact ⟨block054_left_V_pos, block054_right_V_pos⟩

end Block054
end M1817475
end Erdos1038Lean
