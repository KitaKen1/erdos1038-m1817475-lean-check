import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block034

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block034

open Set

def block034W1 : Rat := ((3034332444557773 : Rat) / 1250000000000000)
def block034W2 : Rat := (0 : Rat)
def block034W3 : Rat := (0 : Rat)
def block034W4 : Rat := ((2804609380388413 : Rat) / 10000000000000000)
def block034S1 : Rat := ((18174751 : Rat) / 10000000)
def block034S2 : Rat := ((511587 : Rat) / 200000)
def block034S3 : Rat := ((107000619 : Rat) / 40000000)
def block034S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block034V (y : ℝ) : ℝ :=
  ratPotential block034W1 block034W2 block034W3 block034W4 block034S1 block034S2 block034S3 block034S4 y

def block034LeftParamsCertificate : Bool :=
  allBoxesSameParams block034LeftBoxes block034W1 block034W2 block034W3 block034W4 block034S1 block034S2 block034S3 block034S4

theorem block034LeftParamsCertificate_eq_true :
    block034LeftParamsCertificate = true := by
  native_decide

theorem block034_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block034LeftL : ℝ) (block034LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block034S1 : ℝ))
    (hy2ne : y ≠ (block034S2 : ℝ))
    (hy3ne : y ≠ (block034S3 : ℝ))
    (hy4ne : y ≠ (block034S4 : ℝ)) :
    0 < block034V y := by
  have hcert := block034LeftCertificate_eq_true
  unfold block034LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block034LeftBoxes) (lo := block034LeftL) (hi := block034LeftR)
    (w1 := block034W1) (w2 := block034W2) (w3 := block034W3) (w4 := block034W4)
    (s1 := block034S1) (s2 := block034S2) (s3 := block034S3) (s4 := block034S4)
    hboxes hcover block034LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block034RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block034RightChunk000 block034W1 block034W2 block034W3 block034W4 block034S1 block034S2 block034S3 block034S4

theorem block034RightChunk000ParamsCertificate_eq_true :
    block034RightChunk000ParamsCertificate = true := by
  native_decide

theorem block034_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block034RightChunk000L : ℝ) (block034RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block034S1 : ℝ))
    (hy2ne : y ≠ (block034S2 : ℝ))
    (hy3ne : y ≠ (block034S3 : ℝ))
    (hy4ne : y ≠ (block034S4 : ℝ)) :
    0 < block034V y := by
  have hcert := block034RightChunk000Certificate_eq_true
  unfold block034RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block034RightChunk000) (lo := block034RightChunk000L) (hi := block034RightChunk000R)
    (w1 := block034W1) (w2 := block034W2) (w3 := block034W3) (w4 := block034W4)
    (s1 := block034S1) (s2 := block034S2) (s3 := block034S3) (s4 := block034S4)
    hboxes hcover block034RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block034_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block034RightL : ℝ) (block034RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block034S1 : ℝ))
    (hy2ne : y ≠ (block034S2 : ℝ))
    (hy3ne : y ≠ (block034S3 : ℝ))
    (hy4ne : y ≠ (block034S4 : ℝ)) :
    0 < block034V y := by
  have hL : (block034RightChunk000L : ℝ) = (block034RightL : ℝ) := by
    norm_num [block034RightChunk000L, block034RightL]
  have hR : (block034RightChunk000R : ℝ) = (block034RightR : ℝ) := by
    norm_num [block034RightChunk000R, block034RightR]
  have hyc : y ∈ Icc (block034RightChunk000L : ℝ) (block034RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block034_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block034_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block034LeftL : ℝ) (block034LeftR : ℝ) →
    y ≠ 0 → y ≠ (block034S1 : ℝ) → y ≠ (block034S2 : ℝ) →
    y ≠ (block034S3 : ℝ) → y ≠ (block034S4 : ℝ) → 0 < block034V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block034RightL : ℝ) (block034RightR : ℝ) →
    y ≠ 0 → y ≠ (block034S1 : ℝ) → y ≠ (block034S2 : ℝ) →
    y ≠ (block034S3 : ℝ) → y ≠ (block034S4 : ℝ) → 0 < block034V y)

theorem block034_reallog_certificate_proof :
    block034_reallog_certificate := by
  exact ⟨block034_left_V_pos, block034_right_V_pos⟩

end Block034
end M1817475
end Erdos1038Lean
