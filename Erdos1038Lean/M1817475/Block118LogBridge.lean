import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block118

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block118

open Set

def block118W1 : Rat := ((2368301418248381 : Rat) / 1000000000000000)
def block118W2 : Rat := (0 : Rat)
def block118W3 : Rat := ((8632849908299729 : Rat) / 100000000000000000)
def block118W4 : Rat := ((3267764670508193 : Rat) / 20000000000000000)
def block118S1 : Rat := ((18174751 : Rat) / 10000000)
def block118S2 : Rat := ((511587 : Rat) / 200000)
def block118S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block118S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block118V (y : ℝ) : ℝ :=
  ratPotential block118W1 block118W2 block118W3 block118W4 block118S1 block118S2 block118S3 block118S4 y

def block118LeftParamsCertificate : Bool :=
  allBoxesSameParams block118LeftBoxes block118W1 block118W2 block118W3 block118W4 block118S1 block118S2 block118S3 block118S4

theorem block118LeftParamsCertificate_eq_true :
    block118LeftParamsCertificate = true := by
  native_decide

theorem block118_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block118LeftL : ℝ) (block118LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block118S1 : ℝ))
    (hy2ne : y ≠ (block118S2 : ℝ))
    (hy3ne : y ≠ (block118S3 : ℝ))
    (hy4ne : y ≠ (block118S4 : ℝ)) :
    0 < block118V y := by
  have hcert := block118LeftCertificate_eq_true
  unfold block118LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block118LeftBoxes) (lo := block118LeftL) (hi := block118LeftR)
    (w1 := block118W1) (w2 := block118W2) (w3 := block118W3) (w4 := block118W4)
    (s1 := block118S1) (s2 := block118S2) (s3 := block118S3) (s4 := block118S4)
    hboxes hcover block118LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block118RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block118RightChunk000 block118W1 block118W2 block118W3 block118W4 block118S1 block118S2 block118S3 block118S4

theorem block118RightChunk000ParamsCertificate_eq_true :
    block118RightChunk000ParamsCertificate = true := by
  native_decide

theorem block118_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block118RightChunk000L : ℝ) (block118RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block118S1 : ℝ))
    (hy2ne : y ≠ (block118S2 : ℝ))
    (hy3ne : y ≠ (block118S3 : ℝ))
    (hy4ne : y ≠ (block118S4 : ℝ)) :
    0 < block118V y := by
  have hcert := block118RightChunk000Certificate_eq_true
  unfold block118RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block118RightChunk000) (lo := block118RightChunk000L) (hi := block118RightChunk000R)
    (w1 := block118W1) (w2 := block118W2) (w3 := block118W3) (w4 := block118W4)
    (s1 := block118S1) (s2 := block118S2) (s3 := block118S3) (s4 := block118S4)
    hboxes hcover block118RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block118_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block118RightL : ℝ) (block118RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block118S1 : ℝ))
    (hy2ne : y ≠ (block118S2 : ℝ))
    (hy3ne : y ≠ (block118S3 : ℝ))
    (hy4ne : y ≠ (block118S4 : ℝ)) :
    0 < block118V y := by
  have hL : (block118RightChunk000L : ℝ) = (block118RightL : ℝ) := by
    norm_num [block118RightChunk000L, block118RightL]
  have hR : (block118RightChunk000R : ℝ) = (block118RightR : ℝ) := by
    norm_num [block118RightChunk000R, block118RightR]
  have hyc : y ∈ Icc (block118RightChunk000L : ℝ) (block118RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block118_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block118_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block118LeftL : ℝ) (block118LeftR : ℝ) →
    y ≠ 0 → y ≠ (block118S1 : ℝ) → y ≠ (block118S2 : ℝ) →
    y ≠ (block118S3 : ℝ) → y ≠ (block118S4 : ℝ) → 0 < block118V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block118RightL : ℝ) (block118RightR : ℝ) →
    y ≠ 0 → y ≠ (block118S1 : ℝ) → y ≠ (block118S2 : ℝ) →
    y ≠ (block118S3 : ℝ) → y ≠ (block118S4 : ℝ) → 0 < block118V y)

theorem block118_reallog_certificate_proof :
    block118_reallog_certificate := by
  exact ⟨block118_left_V_pos, block118_right_V_pos⟩

end Block118
end M1817475
end Erdos1038Lean
