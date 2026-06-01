import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block040

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block040

open Set

def block040W1 : Rat := ((25157001121979947 : Rat) / 10000000000000000)
def block040W2 : Rat := (0 : Rat)
def block040W3 : Rat := (0 : Rat)
def block040W4 : Rat := ((3451312913497797 : Rat) / 12500000000000000)
def block040S1 : Rat := ((18174751 : Rat) / 10000000)
def block040S2 : Rat := ((511587 : Rat) / 200000)
def block040S3 : Rat := ((107000619 : Rat) / 40000000)
def block040S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block040V (y : ℝ) : ℝ :=
  ratPotential block040W1 block040W2 block040W3 block040W4 block040S1 block040S2 block040S3 block040S4 y

def block040LeftParamsCertificate : Bool :=
  allBoxesSameParams block040LeftBoxes block040W1 block040W2 block040W3 block040W4 block040S1 block040S2 block040S3 block040S4

theorem block040LeftParamsCertificate_eq_true :
    block040LeftParamsCertificate = true := by
  native_decide

theorem block040_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block040LeftL : ℝ) (block040LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block040S1 : ℝ))
    (hy2ne : y ≠ (block040S2 : ℝ))
    (hy3ne : y ≠ (block040S3 : ℝ))
    (hy4ne : y ≠ (block040S4 : ℝ)) :
    0 < block040V y := by
  have hcert := block040LeftCertificate_eq_true
  unfold block040LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block040LeftBoxes) (lo := block040LeftL) (hi := block040LeftR)
    (w1 := block040W1) (w2 := block040W2) (w3 := block040W3) (w4 := block040W4)
    (s1 := block040S1) (s2 := block040S2) (s3 := block040S3) (s4 := block040S4)
    hboxes hcover block040LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block040RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block040RightChunk000 block040W1 block040W2 block040W3 block040W4 block040S1 block040S2 block040S3 block040S4

theorem block040RightChunk000ParamsCertificate_eq_true :
    block040RightChunk000ParamsCertificate = true := by
  native_decide

theorem block040_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block040RightChunk000L : ℝ) (block040RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block040S1 : ℝ))
    (hy2ne : y ≠ (block040S2 : ℝ))
    (hy3ne : y ≠ (block040S3 : ℝ))
    (hy4ne : y ≠ (block040S4 : ℝ)) :
    0 < block040V y := by
  have hcert := block040RightChunk000Certificate_eq_true
  unfold block040RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block040RightChunk000) (lo := block040RightChunk000L) (hi := block040RightChunk000R)
    (w1 := block040W1) (w2 := block040W2) (w3 := block040W3) (w4 := block040W4)
    (s1 := block040S1) (s2 := block040S2) (s3 := block040S3) (s4 := block040S4)
    hboxes hcover block040RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block040_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block040RightL : ℝ) (block040RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block040S1 : ℝ))
    (hy2ne : y ≠ (block040S2 : ℝ))
    (hy3ne : y ≠ (block040S3 : ℝ))
    (hy4ne : y ≠ (block040S4 : ℝ)) :
    0 < block040V y := by
  have hL : (block040RightChunk000L : ℝ) = (block040RightL : ℝ) := by
    norm_num [block040RightChunk000L, block040RightL]
  have hR : (block040RightChunk000R : ℝ) = (block040RightR : ℝ) := by
    norm_num [block040RightChunk000R, block040RightR]
  have hyc : y ∈ Icc (block040RightChunk000L : ℝ) (block040RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block040_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block040_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block040LeftL : ℝ) (block040LeftR : ℝ) →
    y ≠ 0 → y ≠ (block040S1 : ℝ) → y ≠ (block040S2 : ℝ) →
    y ≠ (block040S3 : ℝ) → y ≠ (block040S4 : ℝ) → 0 < block040V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block040RightL : ℝ) (block040RightR : ℝ) →
    y ≠ 0 → y ≠ (block040S1 : ℝ) → y ≠ (block040S2 : ℝ) →
    y ≠ (block040S3 : ℝ) → y ≠ (block040S4 : ℝ) → 0 < block040V y)

theorem block040_reallog_certificate_proof :
    block040_reallog_certificate := by
  exact ⟨block040_left_V_pos, block040_right_V_pos⟩

end Block040
end M1817475
end Erdos1038Lean
