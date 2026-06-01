import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block323

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block323

open Set

def block323W1 : Rat := ((9323215399291211 : Rat) / 10000000000000000)
def block323W2 : Rat := ((224367527202119 : Rat) / 3125000000000000)
def block323W3 : Rat := ((1560864709004383 : Rat) / 6250000000000000)
def block323W4 : Rat := (0 : Rat)
def block323S1 : Rat := ((18174751 : Rat) / 10000000)
def block323S2 : Rat := ((511587 : Rat) / 200000)
def block323S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block323S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block323V (y : ℝ) : ℝ :=
  ratPotential block323W1 block323W2 block323W3 block323W4 block323S1 block323S2 block323S3 block323S4 y

def block323LeftParamsCertificate : Bool :=
  allBoxesSameParams block323LeftBoxes block323W1 block323W2 block323W3 block323W4 block323S1 block323S2 block323S3 block323S4

theorem block323LeftParamsCertificate_eq_true :
    block323LeftParamsCertificate = true := by
  native_decide

theorem block323_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block323LeftL : ℝ) (block323LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block323S1 : ℝ))
    (hy2ne : y ≠ (block323S2 : ℝ))
    (hy3ne : y ≠ (block323S3 : ℝ))
    (hy4ne : y ≠ (block323S4 : ℝ)) :
    0 < block323V y := by
  have hcert := block323LeftCertificate_eq_true
  unfold block323LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block323LeftBoxes) (lo := block323LeftL) (hi := block323LeftR)
    (w1 := block323W1) (w2 := block323W2) (w3 := block323W3) (w4 := block323W4)
    (s1 := block323S1) (s2 := block323S2) (s3 := block323S3) (s4 := block323S4)
    hboxes hcover block323LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block323RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block323RightChunk000 block323W1 block323W2 block323W3 block323W4 block323S1 block323S2 block323S3 block323S4

theorem block323RightChunk000ParamsCertificate_eq_true :
    block323RightChunk000ParamsCertificate = true := by
  native_decide

theorem block323_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block323RightChunk000L : ℝ) (block323RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block323S1 : ℝ))
    (hy2ne : y ≠ (block323S2 : ℝ))
    (hy3ne : y ≠ (block323S3 : ℝ))
    (hy4ne : y ≠ (block323S4 : ℝ)) :
    0 < block323V y := by
  have hcert := block323RightChunk000Certificate_eq_true
  unfold block323RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block323RightChunk000) (lo := block323RightChunk000L) (hi := block323RightChunk000R)
    (w1 := block323W1) (w2 := block323W2) (w3 := block323W3) (w4 := block323W4)
    (s1 := block323S1) (s2 := block323S2) (s3 := block323S3) (s4 := block323S4)
    hboxes hcover block323RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block323_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block323RightL : ℝ) (block323RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block323S1 : ℝ))
    (hy2ne : y ≠ (block323S2 : ℝ))
    (hy3ne : y ≠ (block323S3 : ℝ))
    (hy4ne : y ≠ (block323S4 : ℝ)) :
    0 < block323V y := by
  have hL : (block323RightChunk000L : ℝ) = (block323RightL : ℝ) := by
    norm_num [block323RightChunk000L, block323RightL]
  have hR : (block323RightChunk000R : ℝ) = (block323RightR : ℝ) := by
    norm_num [block323RightChunk000R, block323RightR]
  have hyc : y ∈ Icc (block323RightChunk000L : ℝ) (block323RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block323_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block323_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block323LeftL : ℝ) (block323LeftR : ℝ) →
    y ≠ 0 → y ≠ (block323S1 : ℝ) → y ≠ (block323S2 : ℝ) →
    y ≠ (block323S3 : ℝ) → y ≠ (block323S4 : ℝ) → 0 < block323V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block323RightL : ℝ) (block323RightR : ℝ) →
    y ≠ 0 → y ≠ (block323S1 : ℝ) → y ≠ (block323S2 : ℝ) →
    y ≠ (block323S3 : ℝ) → y ≠ (block323S4 : ℝ) → 0 < block323V y)

theorem block323_reallog_certificate_proof :
    block323_reallog_certificate := by
  exact ⟨block323_left_V_pos, block323_right_V_pos⟩

end Block323
end M1817475
end Erdos1038Lean
