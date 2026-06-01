import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block435

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block435

open Set

def block435W1 : Rat := ((1282436062464881 : Rat) / 2000000000000000)
def block435W2 : Rat := (0 : Rat)
def block435W3 : Rat := ((7847920041785779 : Rat) / 25000000000000000)
def block435W4 : Rat := ((7686390391952207 : Rat) / 100000000000000000)
def block435S1 : Rat := ((18174751 : Rat) / 10000000)
def block435S2 : Rat := ((511587 : Rat) / 200000)
def block435S3 : Rat := ((131629695625000000093 : Rat) / 50000000000000000000)
def block435S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block435V (y : ℝ) : ℝ :=
  ratPotential block435W1 block435W2 block435W3 block435W4 block435S1 block435S2 block435S3 block435S4 y

def block435LeftParamsCertificate : Bool :=
  allBoxesSameParams block435LeftBoxes block435W1 block435W2 block435W3 block435W4 block435S1 block435S2 block435S3 block435S4

theorem block435LeftParamsCertificate_eq_true :
    block435LeftParamsCertificate = true := by
  native_decide

theorem block435_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block435LeftL : ℝ) (block435LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block435S1 : ℝ))
    (hy2ne : y ≠ (block435S2 : ℝ))
    (hy3ne : y ≠ (block435S3 : ℝ))
    (hy4ne : y ≠ (block435S4 : ℝ)) :
    0 < block435V y := by
  have hcert := block435LeftCertificate_eq_true
  unfold block435LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block435LeftBoxes) (lo := block435LeftL) (hi := block435LeftR)
    (w1 := block435W1) (w2 := block435W2) (w3 := block435W3) (w4 := block435W4)
    (s1 := block435S1) (s2 := block435S2) (s3 := block435S3) (s4 := block435S4)
    hboxes hcover block435LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block435RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block435RightChunk000 block435W1 block435W2 block435W3 block435W4 block435S1 block435S2 block435S3 block435S4

theorem block435RightChunk000ParamsCertificate_eq_true :
    block435RightChunk000ParamsCertificate = true := by
  native_decide

theorem block435_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block435RightChunk000L : ℝ) (block435RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block435S1 : ℝ))
    (hy2ne : y ≠ (block435S2 : ℝ))
    (hy3ne : y ≠ (block435S3 : ℝ))
    (hy4ne : y ≠ (block435S4 : ℝ)) :
    0 < block435V y := by
  have hcert := block435RightChunk000Certificate_eq_true
  unfold block435RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block435RightChunk000) (lo := block435RightChunk000L) (hi := block435RightChunk000R)
    (w1 := block435W1) (w2 := block435W2) (w3 := block435W3) (w4 := block435W4)
    (s1 := block435S1) (s2 := block435S2) (s3 := block435S3) (s4 := block435S4)
    hboxes hcover block435RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block435_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block435RightL : ℝ) (block435RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block435S1 : ℝ))
    (hy2ne : y ≠ (block435S2 : ℝ))
    (hy3ne : y ≠ (block435S3 : ℝ))
    (hy4ne : y ≠ (block435S4 : ℝ)) :
    0 < block435V y := by
  have hL : (block435RightChunk000L : ℝ) = (block435RightL : ℝ) := by
    norm_num [block435RightChunk000L, block435RightL]
  have hR : (block435RightChunk000R : ℝ) = (block435RightR : ℝ) := by
    norm_num [block435RightChunk000R, block435RightR]
  have hyc : y ∈ Icc (block435RightChunk000L : ℝ) (block435RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block435_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block435_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block435LeftL : ℝ) (block435LeftR : ℝ) →
    y ≠ 0 → y ≠ (block435S1 : ℝ) → y ≠ (block435S2 : ℝ) →
    y ≠ (block435S3 : ℝ) → y ≠ (block435S4 : ℝ) → 0 < block435V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block435RightL : ℝ) (block435RightR : ℝ) →
    y ≠ 0 → y ≠ (block435S1 : ℝ) → y ≠ (block435S2 : ℝ) →
    y ≠ (block435S3 : ℝ) → y ≠ (block435S4 : ℝ) → 0 < block435V y)

theorem block435_reallog_certificate_proof :
    block435_reallog_certificate := by
  exact ⟨block435_left_V_pos, block435_right_V_pos⟩

end Block435
end M1817475
end Erdos1038Lean
