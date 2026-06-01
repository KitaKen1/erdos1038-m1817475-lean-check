import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block553

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block553

open Set

def block553W1 : Rat := ((153931445635333 : Rat) / 400000000000000)
def block553W2 : Rat := (0 : Rat)
def block553W3 : Rat := ((9219032639968907 : Rat) / 20000000000000000)
def block553W4 : Rat := (0 : Rat)
def block553S1 : Rat := ((18174751 : Rat) / 10000000)
def block553S2 : Rat := ((511587 : Rat) / 200000)
def block553S3 : Rat := ((129322900982142857337 : Rat) / 50000000000000000000)
def block553S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block553V (y : ℝ) : ℝ :=
  ratPotential block553W1 block553W2 block553W3 block553W4 block553S1 block553S2 block553S3 block553S4 y

def block553LeftParamsCertificate : Bool :=
  allBoxesSameParams block553LeftBoxes block553W1 block553W2 block553W3 block553W4 block553S1 block553S2 block553S3 block553S4

theorem block553LeftParamsCertificate_eq_true :
    block553LeftParamsCertificate = true := by
  native_decide

theorem block553_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block553LeftL : ℝ) (block553LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block553S1 : ℝ))
    (hy2ne : y ≠ (block553S2 : ℝ))
    (hy3ne : y ≠ (block553S3 : ℝ))
    (hy4ne : y ≠ (block553S4 : ℝ)) :
    0 < block553V y := by
  have hcert := block553LeftCertificate_eq_true
  unfold block553LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block553LeftBoxes) (lo := block553LeftL) (hi := block553LeftR)
    (w1 := block553W1) (w2 := block553W2) (w3 := block553W3) (w4 := block553W4)
    (s1 := block553S1) (s2 := block553S2) (s3 := block553S3) (s4 := block553S4)
    hboxes hcover block553LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block553RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block553RightChunk000 block553W1 block553W2 block553W3 block553W4 block553S1 block553S2 block553S3 block553S4

theorem block553RightChunk000ParamsCertificate_eq_true :
    block553RightChunk000ParamsCertificate = true := by
  native_decide

theorem block553_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block553RightChunk000L : ℝ) (block553RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block553S1 : ℝ))
    (hy2ne : y ≠ (block553S2 : ℝ))
    (hy3ne : y ≠ (block553S3 : ℝ))
    (hy4ne : y ≠ (block553S4 : ℝ)) :
    0 < block553V y := by
  have hcert := block553RightChunk000Certificate_eq_true
  unfold block553RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block553RightChunk000) (lo := block553RightChunk000L) (hi := block553RightChunk000R)
    (w1 := block553W1) (w2 := block553W2) (w3 := block553W3) (w4 := block553W4)
    (s1 := block553S1) (s2 := block553S2) (s3 := block553S3) (s4 := block553S4)
    hboxes hcover block553RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block553_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block553RightL : ℝ) (block553RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block553S1 : ℝ))
    (hy2ne : y ≠ (block553S2 : ℝ))
    (hy3ne : y ≠ (block553S3 : ℝ))
    (hy4ne : y ≠ (block553S4 : ℝ)) :
    0 < block553V y := by
  have hL : (block553RightChunk000L : ℝ) = (block553RightL : ℝ) := by
    norm_num [block553RightChunk000L, block553RightL]
  have hR : (block553RightChunk000R : ℝ) = (block553RightR : ℝ) := by
    norm_num [block553RightChunk000R, block553RightR]
  have hyc : y ∈ Icc (block553RightChunk000L : ℝ) (block553RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block553_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block553_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block553LeftL : ℝ) (block553LeftR : ℝ) →
    y ≠ 0 → y ≠ (block553S1 : ℝ) → y ≠ (block553S2 : ℝ) →
    y ≠ (block553S3 : ℝ) → y ≠ (block553S4 : ℝ) → 0 < block553V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block553RightL : ℝ) (block553RightR : ℝ) →
    y ≠ 0 → y ≠ (block553S1 : ℝ) → y ≠ (block553S2 : ℝ) →
    y ≠ (block553S3 : ℝ) → y ≠ (block553S4 : ℝ) → 0 < block553V y)

theorem block553_reallog_certificate_proof :
    block553_reallog_certificate := by
  exact ⟨block553_left_V_pos, block553_right_V_pos⟩

end Block553
end M1817475
end Erdos1038Lean
