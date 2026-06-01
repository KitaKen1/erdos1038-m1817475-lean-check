import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block133

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block133

open Set

def block133W1 : Rat := ((2540708302832049 : Rat) / 1000000000000000)
def block133W2 : Rat := (0 : Rat)
def block133W3 : Rat := ((11068446185197699 : Rat) / 100000000000000000)
def block133W4 : Rat := ((6511601857719479 : Rat) / 50000000000000000)
def block133S1 : Rat := ((18174751 : Rat) / 10000000)
def block133S2 : Rat := ((511587 : Rat) / 200000)
def block133S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block133S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block133V (y : ℝ) : ℝ :=
  ratPotential block133W1 block133W2 block133W3 block133W4 block133S1 block133S2 block133S3 block133S4 y

def block133LeftParamsCertificate : Bool :=
  allBoxesSameParams block133LeftBoxes block133W1 block133W2 block133W3 block133W4 block133S1 block133S2 block133S3 block133S4

theorem block133LeftParamsCertificate_eq_true :
    block133LeftParamsCertificate = true := by
  native_decide

theorem block133_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block133LeftL : ℝ) (block133LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block133S1 : ℝ))
    (hy2ne : y ≠ (block133S2 : ℝ))
    (hy3ne : y ≠ (block133S3 : ℝ))
    (hy4ne : y ≠ (block133S4 : ℝ)) :
    0 < block133V y := by
  have hcert := block133LeftCertificate_eq_true
  unfold block133LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block133LeftBoxes) (lo := block133LeftL) (hi := block133LeftR)
    (w1 := block133W1) (w2 := block133W2) (w3 := block133W3) (w4 := block133W4)
    (s1 := block133S1) (s2 := block133S2) (s3 := block133S3) (s4 := block133S4)
    hboxes hcover block133LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block133RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block133RightChunk000 block133W1 block133W2 block133W3 block133W4 block133S1 block133S2 block133S3 block133S4

theorem block133RightChunk000ParamsCertificate_eq_true :
    block133RightChunk000ParamsCertificate = true := by
  native_decide

theorem block133_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block133RightChunk000L : ℝ) (block133RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block133S1 : ℝ))
    (hy2ne : y ≠ (block133S2 : ℝ))
    (hy3ne : y ≠ (block133S3 : ℝ))
    (hy4ne : y ≠ (block133S4 : ℝ)) :
    0 < block133V y := by
  have hcert := block133RightChunk000Certificate_eq_true
  unfold block133RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block133RightChunk000) (lo := block133RightChunk000L) (hi := block133RightChunk000R)
    (w1 := block133W1) (w2 := block133W2) (w3 := block133W3) (w4 := block133W4)
    (s1 := block133S1) (s2 := block133S2) (s3 := block133S3) (s4 := block133S4)
    hboxes hcover block133RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block133_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block133RightL : ℝ) (block133RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block133S1 : ℝ))
    (hy2ne : y ≠ (block133S2 : ℝ))
    (hy3ne : y ≠ (block133S3 : ℝ))
    (hy4ne : y ≠ (block133S4 : ℝ)) :
    0 < block133V y := by
  have hL : (block133RightChunk000L : ℝ) = (block133RightL : ℝ) := by
    norm_num [block133RightChunk000L, block133RightL]
  have hR : (block133RightChunk000R : ℝ) = (block133RightR : ℝ) := by
    norm_num [block133RightChunk000R, block133RightR]
  have hyc : y ∈ Icc (block133RightChunk000L : ℝ) (block133RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block133_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block133_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block133LeftL : ℝ) (block133LeftR : ℝ) →
    y ≠ 0 → y ≠ (block133S1 : ℝ) → y ≠ (block133S2 : ℝ) →
    y ≠ (block133S3 : ℝ) → y ≠ (block133S4 : ℝ) → 0 < block133V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block133RightL : ℝ) (block133RightR : ℝ) →
    y ≠ 0 → y ≠ (block133S1 : ℝ) → y ≠ (block133S2 : ℝ) →
    y ≠ (block133S3 : ℝ) → y ≠ (block133S4 : ℝ) → 0 < block133V y)

theorem block133_reallog_certificate_proof :
    block133_reallog_certificate := by
  exact ⟨block133_left_V_pos, block133_right_V_pos⟩

end Block133
end M1817475
end Erdos1038Lean
