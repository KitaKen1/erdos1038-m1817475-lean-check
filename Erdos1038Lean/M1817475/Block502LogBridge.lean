import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block502

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block502

open Set

def block502W1 : Rat := ((57044019782941 : Rat) / 125000000000000)
def block502W2 : Rat := (0 : Rat)
def block502W3 : Rat := ((4193092467890167 : Rat) / 10000000000000000)
def block502W4 : Rat := ((2141554677361939 : Rat) / 125000000000000000)
def block502S1 : Rat := ((18174751 : Rat) / 10000000)
def block502S2 : Rat := ((511587 : Rat) / 200000)
def block502S3 : Rat := ((130319905446428571579 : Rat) / 50000000000000000000)
def block502S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block502V (y : ℝ) : ℝ :=
  ratPotential block502W1 block502W2 block502W3 block502W4 block502S1 block502S2 block502S3 block502S4 y

def block502LeftParamsCertificate : Bool :=
  allBoxesSameParams block502LeftBoxes block502W1 block502W2 block502W3 block502W4 block502S1 block502S2 block502S3 block502S4

theorem block502LeftParamsCertificate_eq_true :
    block502LeftParamsCertificate = true := by
  native_decide

theorem block502_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block502LeftL : ℝ) (block502LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block502S1 : ℝ))
    (hy2ne : y ≠ (block502S2 : ℝ))
    (hy3ne : y ≠ (block502S3 : ℝ))
    (hy4ne : y ≠ (block502S4 : ℝ)) :
    0 < block502V y := by
  have hcert := block502LeftCertificate_eq_true
  unfold block502LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block502LeftBoxes) (lo := block502LeftL) (hi := block502LeftR)
    (w1 := block502W1) (w2 := block502W2) (w3 := block502W3) (w4 := block502W4)
    (s1 := block502S1) (s2 := block502S2) (s3 := block502S3) (s4 := block502S4)
    hboxes hcover block502LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block502RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block502RightChunk000 block502W1 block502W2 block502W3 block502W4 block502S1 block502S2 block502S3 block502S4

theorem block502RightChunk000ParamsCertificate_eq_true :
    block502RightChunk000ParamsCertificate = true := by
  native_decide

theorem block502_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block502RightChunk000L : ℝ) (block502RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block502S1 : ℝ))
    (hy2ne : y ≠ (block502S2 : ℝ))
    (hy3ne : y ≠ (block502S3 : ℝ))
    (hy4ne : y ≠ (block502S4 : ℝ)) :
    0 < block502V y := by
  have hcert := block502RightChunk000Certificate_eq_true
  unfold block502RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block502RightChunk000) (lo := block502RightChunk000L) (hi := block502RightChunk000R)
    (w1 := block502W1) (w2 := block502W2) (w3 := block502W3) (w4 := block502W4)
    (s1 := block502S1) (s2 := block502S2) (s3 := block502S3) (s4 := block502S4)
    hboxes hcover block502RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block502_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block502RightL : ℝ) (block502RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block502S1 : ℝ))
    (hy2ne : y ≠ (block502S2 : ℝ))
    (hy3ne : y ≠ (block502S3 : ℝ))
    (hy4ne : y ≠ (block502S4 : ℝ)) :
    0 < block502V y := by
  have hL : (block502RightChunk000L : ℝ) = (block502RightL : ℝ) := by
    norm_num [block502RightChunk000L, block502RightL]
  have hR : (block502RightChunk000R : ℝ) = (block502RightR : ℝ) := by
    norm_num [block502RightChunk000R, block502RightR]
  have hyc : y ∈ Icc (block502RightChunk000L : ℝ) (block502RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block502_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block502_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block502LeftL : ℝ) (block502LeftR : ℝ) →
    y ≠ 0 → y ≠ (block502S1 : ℝ) → y ≠ (block502S2 : ℝ) →
    y ≠ (block502S3 : ℝ) → y ≠ (block502S4 : ℝ) → 0 < block502V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block502RightL : ℝ) (block502RightR : ℝ) →
    y ≠ 0 → y ≠ (block502S1 : ℝ) → y ≠ (block502S2 : ℝ) →
    y ≠ (block502S3 : ℝ) → y ≠ (block502S4 : ℝ) → 0 < block502V y)

theorem block502_reallog_certificate_proof :
    block502_reallog_certificate := by
  exact ⟨block502_left_V_pos, block502_right_V_pos⟩

end Block502
end M1817475
end Erdos1038Lean
