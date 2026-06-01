import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block447

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block447

open Set

def block447W1 : Rat := ((3029493595140643 : Rat) / 5000000000000000)
def block447W2 : Rat := (0 : Rat)
def block447W3 : Rat := ((6583287526971443 : Rat) / 20000000000000000)
def block447W4 : Rat := ((86420082985423 : Rat) / 1250000000000000)
def block447S1 : Rat := ((18174751 : Rat) / 10000000)
def block447S2 : Rat := ((511587 : Rat) / 200000)
def block447S3 : Rat := ((131395106339285714389 : Rat) / 50000000000000000000)
def block447S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block447V (y : ℝ) : ℝ :=
  ratPotential block447W1 block447W2 block447W3 block447W4 block447S1 block447S2 block447S3 block447S4 y

def block447LeftParamsCertificate : Bool :=
  allBoxesSameParams block447LeftBoxes block447W1 block447W2 block447W3 block447W4 block447S1 block447S2 block447S3 block447S4

theorem block447LeftParamsCertificate_eq_true :
    block447LeftParamsCertificate = true := by
  native_decide

theorem block447_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block447LeftL : ℝ) (block447LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block447S1 : ℝ))
    (hy2ne : y ≠ (block447S2 : ℝ))
    (hy3ne : y ≠ (block447S3 : ℝ))
    (hy4ne : y ≠ (block447S4 : ℝ)) :
    0 < block447V y := by
  have hcert := block447LeftCertificate_eq_true
  unfold block447LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block447LeftBoxes) (lo := block447LeftL) (hi := block447LeftR)
    (w1 := block447W1) (w2 := block447W2) (w3 := block447W3) (w4 := block447W4)
    (s1 := block447S1) (s2 := block447S2) (s3 := block447S3) (s4 := block447S4)
    hboxes hcover block447LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block447RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block447RightChunk000 block447W1 block447W2 block447W3 block447W4 block447S1 block447S2 block447S3 block447S4

theorem block447RightChunk000ParamsCertificate_eq_true :
    block447RightChunk000ParamsCertificate = true := by
  native_decide

theorem block447_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block447RightChunk000L : ℝ) (block447RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block447S1 : ℝ))
    (hy2ne : y ≠ (block447S2 : ℝ))
    (hy3ne : y ≠ (block447S3 : ℝ))
    (hy4ne : y ≠ (block447S4 : ℝ)) :
    0 < block447V y := by
  have hcert := block447RightChunk000Certificate_eq_true
  unfold block447RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block447RightChunk000) (lo := block447RightChunk000L) (hi := block447RightChunk000R)
    (w1 := block447W1) (w2 := block447W2) (w3 := block447W3) (w4 := block447W4)
    (s1 := block447S1) (s2 := block447S2) (s3 := block447S3) (s4 := block447S4)
    hboxes hcover block447RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block447_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block447RightL : ℝ) (block447RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block447S1 : ℝ))
    (hy2ne : y ≠ (block447S2 : ℝ))
    (hy3ne : y ≠ (block447S3 : ℝ))
    (hy4ne : y ≠ (block447S4 : ℝ)) :
    0 < block447V y := by
  have hL : (block447RightChunk000L : ℝ) = (block447RightL : ℝ) := by
    norm_num [block447RightChunk000L, block447RightL]
  have hR : (block447RightChunk000R : ℝ) = (block447RightR : ℝ) := by
    norm_num [block447RightChunk000R, block447RightR]
  have hyc : y ∈ Icc (block447RightChunk000L : ℝ) (block447RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block447_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block447_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block447LeftL : ℝ) (block447LeftR : ℝ) →
    y ≠ 0 → y ≠ (block447S1 : ℝ) → y ≠ (block447S2 : ℝ) →
    y ≠ (block447S3 : ℝ) → y ≠ (block447S4 : ℝ) → 0 < block447V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block447RightL : ℝ) (block447RightR : ℝ) →
    y ≠ 0 → y ≠ (block447S1 : ℝ) → y ≠ (block447S2 : ℝ) →
    y ≠ (block447S3 : ℝ) → y ≠ (block447S4 : ℝ) → 0 < block447V y)

theorem block447_reallog_certificate_proof :
    block447_reallog_certificate := by
  exact ⟨block447_left_V_pos, block447_right_V_pos⟩

end Block447
end M1817475
end Erdos1038Lean
