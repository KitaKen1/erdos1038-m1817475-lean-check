import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block500

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block500

open Set

def block500W1 : Rat := ((4617353816668423 : Rat) / 10000000000000000)
def block500W2 : Rat := (0 : Rat)
def block500W3 : Rat := ((20751580599168823 : Rat) / 50000000000000000)
def block500W4 : Rat := ((2478249606739973 : Rat) / 125000000000000000)
def block500S1 : Rat := ((18174751 : Rat) / 10000000)
def block500S2 : Rat := ((511587 : Rat) / 200000)
def block500S3 : Rat := ((130359003660714285863 : Rat) / 50000000000000000000)
def block500S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block500V (y : ℝ) : ℝ :=
  ratPotential block500W1 block500W2 block500W3 block500W4 block500S1 block500S2 block500S3 block500S4 y

def block500LeftParamsCertificate : Bool :=
  allBoxesSameParams block500LeftBoxes block500W1 block500W2 block500W3 block500W4 block500S1 block500S2 block500S3 block500S4

theorem block500LeftParamsCertificate_eq_true :
    block500LeftParamsCertificate = true := by
  native_decide

theorem block500_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block500LeftL : ℝ) (block500LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block500S1 : ℝ))
    (hy2ne : y ≠ (block500S2 : ℝ))
    (hy3ne : y ≠ (block500S3 : ℝ))
    (hy4ne : y ≠ (block500S4 : ℝ)) :
    0 < block500V y := by
  have hcert := block500LeftCertificate_eq_true
  unfold block500LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block500LeftBoxes) (lo := block500LeftL) (hi := block500LeftR)
    (w1 := block500W1) (w2 := block500W2) (w3 := block500W3) (w4 := block500W4)
    (s1 := block500S1) (s2 := block500S2) (s3 := block500S3) (s4 := block500S4)
    hboxes hcover block500LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block500RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block500RightChunk000 block500W1 block500W2 block500W3 block500W4 block500S1 block500S2 block500S3 block500S4

theorem block500RightChunk000ParamsCertificate_eq_true :
    block500RightChunk000ParamsCertificate = true := by
  native_decide

theorem block500_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block500RightChunk000L : ℝ) (block500RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block500S1 : ℝ))
    (hy2ne : y ≠ (block500S2 : ℝ))
    (hy3ne : y ≠ (block500S3 : ℝ))
    (hy4ne : y ≠ (block500S4 : ℝ)) :
    0 < block500V y := by
  have hcert := block500RightChunk000Certificate_eq_true
  unfold block500RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block500RightChunk000) (lo := block500RightChunk000L) (hi := block500RightChunk000R)
    (w1 := block500W1) (w2 := block500W2) (w3 := block500W3) (w4 := block500W4)
    (s1 := block500S1) (s2 := block500S2) (s3 := block500S3) (s4 := block500S4)
    hboxes hcover block500RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block500_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block500RightL : ℝ) (block500RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block500S1 : ℝ))
    (hy2ne : y ≠ (block500S2 : ℝ))
    (hy3ne : y ≠ (block500S3 : ℝ))
    (hy4ne : y ≠ (block500S4 : ℝ)) :
    0 < block500V y := by
  have hL : (block500RightChunk000L : ℝ) = (block500RightL : ℝ) := by
    norm_num [block500RightChunk000L, block500RightL]
  have hR : (block500RightChunk000R : ℝ) = (block500RightR : ℝ) := by
    norm_num [block500RightChunk000R, block500RightR]
  have hyc : y ∈ Icc (block500RightChunk000L : ℝ) (block500RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block500_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block500_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block500LeftL : ℝ) (block500LeftR : ℝ) →
    y ≠ 0 → y ≠ (block500S1 : ℝ) → y ≠ (block500S2 : ℝ) →
    y ≠ (block500S3 : ℝ) → y ≠ (block500S4 : ℝ) → 0 < block500V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block500RightL : ℝ) (block500RightR : ℝ) →
    y ≠ 0 → y ≠ (block500S1 : ℝ) → y ≠ (block500S2 : ℝ) →
    y ≠ (block500S3 : ℝ) → y ≠ (block500S4 : ℝ) → 0 < block500V y)

theorem block500_reallog_certificate_proof :
    block500_reallog_certificate := by
  exact ⟨block500_left_V_pos, block500_right_V_pos⟩

end Block500
end M1817475
end Erdos1038Lean
