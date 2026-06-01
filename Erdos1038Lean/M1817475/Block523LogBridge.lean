import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block523

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block523

open Set

def block523W1 : Rat := ((259465211066279 : Rat) / 625000000000000)
def block523W2 : Rat := (0 : Rat)
def block523W3 : Rat := ((22476992833157153 : Rat) / 50000000000000000)
def block523W4 : Rat := (0 : Rat)
def block523S1 : Rat := ((18174751 : Rat) / 10000000)
def block523S2 : Rat := ((511587 : Rat) / 200000)
def block523S3 : Rat := ((129909374196428571597 : Rat) / 50000000000000000000)
def block523S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block523V (y : ℝ) : ℝ :=
  ratPotential block523W1 block523W2 block523W3 block523W4 block523S1 block523S2 block523S3 block523S4 y

def block523LeftParamsCertificate : Bool :=
  allBoxesSameParams block523LeftBoxes block523W1 block523W2 block523W3 block523W4 block523S1 block523S2 block523S3 block523S4

theorem block523LeftParamsCertificate_eq_true :
    block523LeftParamsCertificate = true := by
  native_decide

theorem block523_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block523LeftL : ℝ) (block523LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block523S1 : ℝ))
    (hy2ne : y ≠ (block523S2 : ℝ))
    (hy3ne : y ≠ (block523S3 : ℝ))
    (hy4ne : y ≠ (block523S4 : ℝ)) :
    0 < block523V y := by
  have hcert := block523LeftCertificate_eq_true
  unfold block523LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block523LeftBoxes) (lo := block523LeftL) (hi := block523LeftR)
    (w1 := block523W1) (w2 := block523W2) (w3 := block523W3) (w4 := block523W4)
    (s1 := block523S1) (s2 := block523S2) (s3 := block523S3) (s4 := block523S4)
    hboxes hcover block523LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block523RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block523RightChunk000 block523W1 block523W2 block523W3 block523W4 block523S1 block523S2 block523S3 block523S4

theorem block523RightChunk000ParamsCertificate_eq_true :
    block523RightChunk000ParamsCertificate = true := by
  native_decide

theorem block523_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block523RightChunk000L : ℝ) (block523RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block523S1 : ℝ))
    (hy2ne : y ≠ (block523S2 : ℝ))
    (hy3ne : y ≠ (block523S3 : ℝ))
    (hy4ne : y ≠ (block523S4 : ℝ)) :
    0 < block523V y := by
  have hcert := block523RightChunk000Certificate_eq_true
  unfold block523RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block523RightChunk000) (lo := block523RightChunk000L) (hi := block523RightChunk000R)
    (w1 := block523W1) (w2 := block523W2) (w3 := block523W3) (w4 := block523W4)
    (s1 := block523S1) (s2 := block523S2) (s3 := block523S3) (s4 := block523S4)
    hboxes hcover block523RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block523_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block523RightL : ℝ) (block523RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block523S1 : ℝ))
    (hy2ne : y ≠ (block523S2 : ℝ))
    (hy3ne : y ≠ (block523S3 : ℝ))
    (hy4ne : y ≠ (block523S4 : ℝ)) :
    0 < block523V y := by
  have hL : (block523RightChunk000L : ℝ) = (block523RightL : ℝ) := by
    norm_num [block523RightChunk000L, block523RightL]
  have hR : (block523RightChunk000R : ℝ) = (block523RightR : ℝ) := by
    norm_num [block523RightChunk000R, block523RightR]
  have hyc : y ∈ Icc (block523RightChunk000L : ℝ) (block523RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block523_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block523_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block523LeftL : ℝ) (block523LeftR : ℝ) →
    y ≠ 0 → y ≠ (block523S1 : ℝ) → y ≠ (block523S2 : ℝ) →
    y ≠ (block523S3 : ℝ) → y ≠ (block523S4 : ℝ) → 0 < block523V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block523RightL : ℝ) (block523RightR : ℝ) →
    y ≠ 0 → y ≠ (block523S1 : ℝ) → y ≠ (block523S2 : ℝ) →
    y ≠ (block523S3 : ℝ) → y ≠ (block523S4 : ℝ) → 0 < block523V y)

theorem block523_reallog_certificate_proof :
    block523_reallog_certificate := by
  exact ⟨block523_left_V_pos, block523_right_V_pos⟩

end Block523
end M1817475
end Erdos1038Lean
