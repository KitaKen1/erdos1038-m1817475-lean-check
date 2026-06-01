import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block109

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block109

open Set

def block109W1 : Rat := ((25574663938190683 : Rat) / 10000000000000000)
def block109W2 : Rat := (0 : Rat)
def block109W3 : Rat := ((6213828297881151 : Rat) / 100000000000000000)
def block109W4 : Rat := ((230035482125877 : Rat) / 1250000000000000)
def block109S1 : Rat := ((18174751 : Rat) / 10000000)
def block109S2 : Rat := ((511587 : Rat) / 200000)
def block109S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block109S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block109V (y : ℝ) : ℝ :=
  ratPotential block109W1 block109W2 block109W3 block109W4 block109S1 block109S2 block109S3 block109S4 y

def block109LeftParamsCertificate : Bool :=
  allBoxesSameParams block109LeftBoxes block109W1 block109W2 block109W3 block109W4 block109S1 block109S2 block109S3 block109S4

theorem block109LeftParamsCertificate_eq_true :
    block109LeftParamsCertificate = true := by
  native_decide

theorem block109_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block109LeftL : ℝ) (block109LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block109S1 : ℝ))
    (hy2ne : y ≠ (block109S2 : ℝ))
    (hy3ne : y ≠ (block109S3 : ℝ))
    (hy4ne : y ≠ (block109S4 : ℝ)) :
    0 < block109V y := by
  have hcert := block109LeftCertificate_eq_true
  unfold block109LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block109LeftBoxes) (lo := block109LeftL) (hi := block109LeftR)
    (w1 := block109W1) (w2 := block109W2) (w3 := block109W3) (w4 := block109W4)
    (s1 := block109S1) (s2 := block109S2) (s3 := block109S3) (s4 := block109S4)
    hboxes hcover block109LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block109RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block109RightChunk000 block109W1 block109W2 block109W3 block109W4 block109S1 block109S2 block109S3 block109S4

theorem block109RightChunk000ParamsCertificate_eq_true :
    block109RightChunk000ParamsCertificate = true := by
  native_decide

theorem block109_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block109RightChunk000L : ℝ) (block109RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block109S1 : ℝ))
    (hy2ne : y ≠ (block109S2 : ℝ))
    (hy3ne : y ≠ (block109S3 : ℝ))
    (hy4ne : y ≠ (block109S4 : ℝ)) :
    0 < block109V y := by
  have hcert := block109RightChunk000Certificate_eq_true
  unfold block109RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block109RightChunk000) (lo := block109RightChunk000L) (hi := block109RightChunk000R)
    (w1 := block109W1) (w2 := block109W2) (w3 := block109W3) (w4 := block109W4)
    (s1 := block109S1) (s2 := block109S2) (s3 := block109S3) (s4 := block109S4)
    hboxes hcover block109RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block109_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block109RightL : ℝ) (block109RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block109S1 : ℝ))
    (hy2ne : y ≠ (block109S2 : ℝ))
    (hy3ne : y ≠ (block109S3 : ℝ))
    (hy4ne : y ≠ (block109S4 : ℝ)) :
    0 < block109V y := by
  have hL : (block109RightChunk000L : ℝ) = (block109RightL : ℝ) := by
    norm_num [block109RightChunk000L, block109RightL]
  have hR : (block109RightChunk000R : ℝ) = (block109RightR : ℝ) := by
    norm_num [block109RightChunk000R, block109RightR]
  have hyc : y ∈ Icc (block109RightChunk000L : ℝ) (block109RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block109_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block109_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block109LeftL : ℝ) (block109LeftR : ℝ) →
    y ≠ 0 → y ≠ (block109S1 : ℝ) → y ≠ (block109S2 : ℝ) →
    y ≠ (block109S3 : ℝ) → y ≠ (block109S4 : ℝ) → 0 < block109V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block109RightL : ℝ) (block109RightR : ℝ) →
    y ≠ 0 → y ≠ (block109S1 : ℝ) → y ≠ (block109S2 : ℝ) →
    y ≠ (block109S3 : ℝ) → y ≠ (block109S4 : ℝ) → 0 < block109V y)

theorem block109_reallog_certificate_proof :
    block109_reallog_certificate := by
  exact ⟨block109_left_V_pos, block109_right_V_pos⟩

end Block109
end M1817475
end Erdos1038Lean
