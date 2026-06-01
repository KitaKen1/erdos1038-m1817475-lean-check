import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block558

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block558

open Set

def block558W1 : Rat := ((475041309215653 : Rat) / 1250000000000000)
def block558W2 : Rat := (0 : Rat)
def block558W3 : Rat := ((46286455709254987 : Rat) / 100000000000000000)
def block558W4 : Rat := (0 : Rat)
def block558S1 : Rat := ((18174751 : Rat) / 10000000)
def block558S2 : Rat := ((511587 : Rat) / 200000)
def block558S3 : Rat := ((129225155446428571627 : Rat) / 50000000000000000000)
def block558S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block558V (y : ℝ) : ℝ :=
  ratPotential block558W1 block558W2 block558W3 block558W4 block558S1 block558S2 block558S3 block558S4 y

def block558LeftParamsCertificate : Bool :=
  allBoxesSameParams block558LeftBoxes block558W1 block558W2 block558W3 block558W4 block558S1 block558S2 block558S3 block558S4

theorem block558LeftParamsCertificate_eq_true :
    block558LeftParamsCertificate = true := by
  native_decide

theorem block558_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block558LeftL : ℝ) (block558LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block558S1 : ℝ))
    (hy2ne : y ≠ (block558S2 : ℝ))
    (hy3ne : y ≠ (block558S3 : ℝ))
    (hy4ne : y ≠ (block558S4 : ℝ)) :
    0 < block558V y := by
  have hcert := block558LeftCertificate_eq_true
  unfold block558LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block558LeftBoxes) (lo := block558LeftL) (hi := block558LeftR)
    (w1 := block558W1) (w2 := block558W2) (w3 := block558W3) (w4 := block558W4)
    (s1 := block558S1) (s2 := block558S2) (s3 := block558S3) (s4 := block558S4)
    hboxes hcover block558LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block558RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block558RightChunk000 block558W1 block558W2 block558W3 block558W4 block558S1 block558S2 block558S3 block558S4

theorem block558RightChunk000ParamsCertificate_eq_true :
    block558RightChunk000ParamsCertificate = true := by
  native_decide

theorem block558_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block558RightChunk000L : ℝ) (block558RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block558S1 : ℝ))
    (hy2ne : y ≠ (block558S2 : ℝ))
    (hy3ne : y ≠ (block558S3 : ℝ))
    (hy4ne : y ≠ (block558S4 : ℝ)) :
    0 < block558V y := by
  have hcert := block558RightChunk000Certificate_eq_true
  unfold block558RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block558RightChunk000) (lo := block558RightChunk000L) (hi := block558RightChunk000R)
    (w1 := block558W1) (w2 := block558W2) (w3 := block558W3) (w4 := block558W4)
    (s1 := block558S1) (s2 := block558S2) (s3 := block558S3) (s4 := block558S4)
    hboxes hcover block558RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block558_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block558RightL : ℝ) (block558RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block558S1 : ℝ))
    (hy2ne : y ≠ (block558S2 : ℝ))
    (hy3ne : y ≠ (block558S3 : ℝ))
    (hy4ne : y ≠ (block558S4 : ℝ)) :
    0 < block558V y := by
  have hL : (block558RightChunk000L : ℝ) = (block558RightL : ℝ) := by
    norm_num [block558RightChunk000L, block558RightL]
  have hR : (block558RightChunk000R : ℝ) = (block558RightR : ℝ) := by
    norm_num [block558RightChunk000R, block558RightR]
  have hyc : y ∈ Icc (block558RightChunk000L : ℝ) (block558RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block558_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block558_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block558LeftL : ℝ) (block558LeftR : ℝ) →
    y ≠ 0 → y ≠ (block558S1 : ℝ) → y ≠ (block558S2 : ℝ) →
    y ≠ (block558S3 : ℝ) → y ≠ (block558S4 : ℝ) → 0 < block558V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block558RightL : ℝ) (block558RightR : ℝ) →
    y ≠ 0 → y ≠ (block558S1 : ℝ) → y ≠ (block558S2 : ℝ) →
    y ≠ (block558S3 : ℝ) → y ≠ (block558S4 : ℝ) → 0 < block558V y)

theorem block558_reallog_certificate_proof :
    block558_reallog_certificate := by
  exact ⟨block558_left_V_pos, block558_right_V_pos⟩

end Block558
end M1817475
end Erdos1038Lean
