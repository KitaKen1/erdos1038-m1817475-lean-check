import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block432

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block432

open Set

def block432W1 : Rat := ((6499475670188821 : Rat) / 10000000000000000)
def block432W2 : Rat := (0 : Rat)
def block432W3 : Rat := ((15525284718257887 : Rat) / 50000000000000000)
def block432W4 : Rat := ((3924180678367257 : Rat) / 50000000000000000)
def block432S1 : Rat := ((18174751 : Rat) / 10000000)
def block432S2 : Rat := ((511587 : Rat) / 200000)
def block432S3 : Rat := ((131688342946428571519 : Rat) / 50000000000000000000)
def block432S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block432V (y : ℝ) : ℝ :=
  ratPotential block432W1 block432W2 block432W3 block432W4 block432S1 block432S2 block432S3 block432S4 y

def block432LeftParamsCertificate : Bool :=
  allBoxesSameParams block432LeftBoxes block432W1 block432W2 block432W3 block432W4 block432S1 block432S2 block432S3 block432S4

theorem block432LeftParamsCertificate_eq_true :
    block432LeftParamsCertificate = true := by
  native_decide

theorem block432_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block432LeftL : ℝ) (block432LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block432S1 : ℝ))
    (hy2ne : y ≠ (block432S2 : ℝ))
    (hy3ne : y ≠ (block432S3 : ℝ))
    (hy4ne : y ≠ (block432S4 : ℝ)) :
    0 < block432V y := by
  have hcert := block432LeftCertificate_eq_true
  unfold block432LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block432LeftBoxes) (lo := block432LeftL) (hi := block432LeftR)
    (w1 := block432W1) (w2 := block432W2) (w3 := block432W3) (w4 := block432W4)
    (s1 := block432S1) (s2 := block432S2) (s3 := block432S3) (s4 := block432S4)
    hboxes hcover block432LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block432RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block432RightChunk000 block432W1 block432W2 block432W3 block432W4 block432S1 block432S2 block432S3 block432S4

theorem block432RightChunk000ParamsCertificate_eq_true :
    block432RightChunk000ParamsCertificate = true := by
  native_decide

theorem block432_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block432RightChunk000L : ℝ) (block432RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block432S1 : ℝ))
    (hy2ne : y ≠ (block432S2 : ℝ))
    (hy3ne : y ≠ (block432S3 : ℝ))
    (hy4ne : y ≠ (block432S4 : ℝ)) :
    0 < block432V y := by
  have hcert := block432RightChunk000Certificate_eq_true
  unfold block432RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block432RightChunk000) (lo := block432RightChunk000L) (hi := block432RightChunk000R)
    (w1 := block432W1) (w2 := block432W2) (w3 := block432W3) (w4 := block432W4)
    (s1 := block432S1) (s2 := block432S2) (s3 := block432S3) (s4 := block432S4)
    hboxes hcover block432RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block432_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block432RightL : ℝ) (block432RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block432S1 : ℝ))
    (hy2ne : y ≠ (block432S2 : ℝ))
    (hy3ne : y ≠ (block432S3 : ℝ))
    (hy4ne : y ≠ (block432S4 : ℝ)) :
    0 < block432V y := by
  have hL : (block432RightChunk000L : ℝ) = (block432RightL : ℝ) := by
    norm_num [block432RightChunk000L, block432RightL]
  have hR : (block432RightChunk000R : ℝ) = (block432RightR : ℝ) := by
    norm_num [block432RightChunk000R, block432RightR]
  have hyc : y ∈ Icc (block432RightChunk000L : ℝ) (block432RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block432_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block432_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block432LeftL : ℝ) (block432LeftR : ℝ) →
    y ≠ 0 → y ≠ (block432S1 : ℝ) → y ≠ (block432S2 : ℝ) →
    y ≠ (block432S3 : ℝ) → y ≠ (block432S4 : ℝ) → 0 < block432V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block432RightL : ℝ) (block432RightR : ℝ) →
    y ≠ 0 → y ≠ (block432S1 : ℝ) → y ≠ (block432S2 : ℝ) →
    y ≠ (block432S3 : ℝ) → y ≠ (block432S4 : ℝ) → 0 < block432V y)

theorem block432_reallog_certificate_proof :
    block432_reallog_certificate := by
  exact ⟨block432_left_V_pos, block432_right_V_pos⟩

end Block432
end M1817475
end Erdos1038Lean
